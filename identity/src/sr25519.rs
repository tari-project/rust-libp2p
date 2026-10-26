//! Sr25519 keys.
//!
//! Sr25519 is Schnorr over the Ristretto255 group, `s·G = R + e·P`, with the challenge `e` drawn
//! from a Merlin transcript that commits to a signing context. Signatures are byte-compatible with
//! [schnorrkel](https://github.com/w3f/schnorrkel), the reference implementation: every signature
//! made here verifies there under [`SIGNING_CONTEXT`], and the reverse.
//!
//! Keys are bare Ristretto255 scalars and points. A secret key is the canonical encoding of its
//! scalar `k` and its public key is `k·G`, so a key managed by any Ristretto255 library is usable
//! here unchanged. Schnorrkel's 32-byte mini secret keys are a seed format and must first be
//! expanded to their scalar.

use core::{cmp, fmt, hash};

use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::IsIdentity,
};
use merlin::Transcript;
use rand::Rng as _;
use zeroize::{Zeroize, Zeroizing};

use super::error::DecodingError;

/// The signing context every libp2p sr25519 signature commits to.
pub const SIGNING_CONTEXT: &[u8] = b"libp2p";

/// The bit set in the last byte of a 64-byte sr25519 signature, marking it as schnorrkel-encoded.
const SIGNATURE_MARKER: u8 = 0x80;

/// An Sr25519 keypair.
#[derive(Clone)]
pub struct Keypair {
    secret: SecretKey,
    public: PublicKey,
}

impl Keypair {
    /// Generate a new random Sr25519 keypair.
    #[cfg(feature = "rand")]
    pub fn generate() -> Keypair {
        Keypair::from(SecretKey::generate())
    }

    /// Convert the keypair into a byte array. This is the secret key alone, since the public key
    /// derives from it.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.secret.to_bytes()
    }

    /// Try to parse a keypair from the format produced by [`Keypair::to_bytes`], zeroing the input
    /// on success.
    pub fn try_from_bytes(kp: &mut [u8]) -> Result<Keypair, DecodingError> {
        SecretKey::try_from_bytes(kp).map(Keypair::from)
    }

    /// Sign a message using the private key of this keypair.
    pub fn sign(&self, msg: &[u8]) -> Vec<u8> {
        self.sign_in(SIGNING_CONTEXT, msg).to_vec()
    }

    fn sign_in(&self, context: &[u8], msg: &[u8]) -> [u8; 64] {
        let nonce = self.secret.signing_nonce(context, msg);
        let public_nonce = RistrettoPoint::mul_base(&nonce).compress();
        let e = challenge(context, &self.public.compressed, &public_nonce, msg);
        let s = *nonce + e * self.secret.0;

        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(public_nonce.as_bytes());
        sig[32..].copy_from_slice(s.as_bytes());
        sig[63] |= SIGNATURE_MARKER;
        sig
    }

    /// Get the public key of this keypair.
    pub fn public(&self) -> PublicKey {
        self.public.clone()
    }

    /// Get the secret key of this keypair.
    pub fn secret(&self) -> SecretKey {
        self.secret.clone()
    }
}

impl fmt::Debug for Keypair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Keypair")
            .field("public", &self.public)
            .finish()
    }
}

/// Demote an Sr25519 keypair to a secret key.
impl From<Keypair> for SecretKey {
    fn from(kp: Keypair) -> SecretKey {
        kp.secret
    }
}

/// Promote an Sr25519 secret key into a keypair.
impl From<SecretKey> for Keypair {
    fn from(secret: SecretKey) -> Keypair {
        let point = RistrettoPoint::mul_base(&secret.0);
        Keypair {
            public: PublicKey {
                compressed: point.compress(),
                point,
            },
            secret,
        }
    }
}

/// An Sr25519 public key.
#[derive(Clone)]
pub struct PublicKey {
    compressed: CompressedRistretto,
    point: RistrettoPoint,
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PublicKey(compressed): ")?;
        for byte in self.compressed.as_bytes() {
            write!(f, "{byte:x}")?;
        }
        Ok(())
    }
}

impl cmp::PartialEq for PublicKey {
    fn eq(&self, other: &Self) -> bool {
        self.compressed.as_bytes().eq(other.compressed.as_bytes())
    }
}

impl cmp::Eq for PublicKey {}

impl hash::Hash for PublicKey {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.compressed.as_bytes().hash(state);
    }
}

impl cmp::PartialOrd for PublicKey {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for PublicKey {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.compressed.as_bytes().cmp(other.compressed.as_bytes())
    }
}

impl PublicKey {
    /// Verify the Sr25519 signature on a message using the public key.
    pub fn verify(&self, msg: &[u8], sig: &[u8]) -> bool {
        self.verify_in(SIGNING_CONTEXT, msg, sig)
    }

    /// The identity key verifies nothing: under it the equation degenerates to `s·G = R`, which
    /// anyone can satisfy.
    fn verify_in(&self, context: &[u8], msg: &[u8], sig: &[u8]) -> bool {
        if self.point.is_identity() {
            return false;
        }
        let Some((public_nonce, s)) = decode_signature(sig) else {
            return false;
        };
        let e = challenge(context, &self.compressed, &public_nonce, msg);
        // Comparing encodings rejects a non-canonical `R`, since a compressed point is canonical.
        RistrettoPoint::vartime_double_scalar_mul_basepoint(&-e, &self.point, &s).compress()
            == public_nonce
    }

    /// Convert the public key to its 32-byte compressed Ristretto encoding.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.compressed.to_bytes()
    }

    /// Try to parse a public key from a byte array containing the actual key as produced by
    /// `to_bytes`. Every canonically encoded point parses, so a PeerId derives from any
    /// Ristretto255 public key.
    pub fn try_from_bytes(k: &[u8]) -> Result<PublicKey, DecodingError> {
        let compressed = CompressedRistretto::from_slice(k)
            .map_err(|e| DecodingError::failed_to_parse("Sr25519 public key", e))?;
        let point = compressed
            .decompress()
            .ok_or_else(|| invalid("Sr25519 public key"))?;
        Ok(PublicKey { compressed, point })
    }
}

/// An Sr25519 secret key.
#[derive(Clone)]
pub struct SecretKey(Scalar);

impl Drop for SecretKey {
    fn drop(&mut self) {
        self.0.zeroize();
    }
}

/// View the bytes of the secret key.
impl AsRef<[u8]> for SecretKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SecretKey")
    }
}

impl SecretKey {
    /// Generate a new Sr25519 secret key.
    #[cfg(feature = "rand")]
    pub fn generate() -> SecretKey {
        let mut wide = Zeroizing::new([0u8; 64]);
        rand::rng().fill_bytes(wide.as_mut());
        SecretKey(Scalar::from_bytes_mod_order_wide(&wide))
    }

    /// Try to parse an Sr25519 secret key from a byte slice containing the canonical encoding of
    /// a non-zero scalar, zeroing the input on success.
    pub fn try_from_bytes(mut sk_bytes: impl AsMut<[u8]>) -> Result<SecretKey, DecodingError> {
        let sk_bytes = sk_bytes.as_mut();
        let bytes = Zeroizing::new(
            <[u8; 32]>::try_from(&*sk_bytes)
                .map_err(|e| DecodingError::failed_to_parse("Sr25519 secret key", e))?,
        );
        let secret = Option::<Scalar>::from(Scalar::from_canonical_bytes(*bytes))
            .filter(|s| *s != Scalar::ZERO)
            .ok_or_else(|| invalid("Sr25519 secret key"))?;
        sk_bytes.zeroize();
        Ok(SecretKey(secret))
    }

    pub(crate) fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// A hedged signing nonce, derived from the context, the secret key, the message and fresh
    /// randomness. With a working RNG it is uniformly random; with a failed or repeating one it
    /// still differs across messages, so a weak RNG alone cannot make one key sign two messages
    /// under the same nonce.
    fn signing_nonce(&self, context: &[u8], msg: &[u8]) -> Zeroizing<Scalar> {
        let mut randomness = Zeroizing::new([0u8; 32]);
        rand::rng().fill_bytes(randomness.as_mut());
        let mut t = Transcript::new(b"libp2p-sr25519-signing-nonce");
        t.append_message(b"context", context);
        t.append_message(b"secret", self.0.as_bytes());
        t.append_message(b"message", msg);
        t.append_message(b"randomness", randomness.as_ref());
        let mut wide = Zeroizing::new([0u8; 64]);
        t.challenge_bytes(b"nonce", wide.as_mut());
        Zeroizing::new(Scalar::from_bytes_mod_order_wide(&wide))
    }
}

/// The challenge `e`: schnorrkel's `signing_context(context).bytes(msg)` transcript followed by its
/// `Schnorr-sig` protocol labels, which commit to the public key before the public nonce.
fn challenge(
    context: &[u8],
    public_key: &CompressedRistretto,
    public_nonce: &CompressedRistretto,
    msg: &[u8],
) -> Scalar {
    let mut t = Transcript::new(b"SigningContext");
    t.append_message(b"", context);
    t.append_message(b"sign-bytes", msg);
    t.append_message(b"proto-name", b"Schnorr-sig");
    t.append_message(b"sign:pk", public_key.as_bytes());
    t.append_message(b"sign:R", public_nonce.as_bytes());
    let mut wide = [0u8; 64];
    t.challenge_bytes(b"sign:c", &mut wide);
    Scalar::from_bytes_mod_order_wide(&wide)
}

/// The public nonce `R` and scalar `s` of a 64-byte signature, or `None` when the marker bit is
/// absent or `s` is not canonically encoded.
fn decode_signature(sig: &[u8]) -> Option<(CompressedRistretto, Scalar)> {
    let sig = <&[u8; 64]>::try_from(sig).ok()?;
    if sig[63] & SIGNATURE_MARKER == 0 {
        return None;
    }
    let public_nonce = CompressedRistretto::from_slice(&sig[..32]).ok()?;
    let mut s = [0u8; 32];
    s.copy_from_slice(&sig[32..]);
    s[31] &= !SIGNATURE_MARKER;
    let s = Option::<Scalar>::from(Scalar::from_canonical_bytes(s))?;
    Some((public_nonce, s))
}

fn invalid(what: &'static str) -> DecodingError {
    DecodingError::failed_to_parse::<core::convert::Infallible, _>(what, None)
}

#[cfg(test)]
mod tests {
    use quickcheck::*;
    use schnorrkel::{ExpansionMode, MiniSecretKey, signing_context};

    use super::*;

    fn eq_keypairs(kp1: &Keypair, kp2: &Keypair) -> bool {
        kp1.public() == kp2.public() && kp1.to_bytes() == kp2.to_bytes()
    }

    fn schnorrkel_keypair(seed: u8) -> schnorrkel::Keypair {
        MiniSecretKey::from_bytes(&[seed; 32])
            .unwrap()
            .expand_to_keypair(ExpansionMode::Ed25519)
    }

    #[test]
    #[cfg(feature = "rand")]
    fn sr25519_keypair_encode_decode() {
        fn prop() -> bool {
            let kp1 = Keypair::generate();
            let mut kp1_enc = kp1.to_bytes();
            let kp2 = Keypair::try_from_bytes(&mut kp1_enc).unwrap();
            eq_keypairs(&kp1, &kp2) && kp1_enc.iter().all(|b| *b == 0)
        }
        QuickCheck::new().tests(10).quickcheck(prop as fn() -> _);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn sr25519_keypair_from_secret() {
        fn prop() -> bool {
            let kp1 = Keypair::generate();
            let mut sk = kp1.secret().to_bytes();
            let kp2 = Keypair::from(SecretKey::try_from_bytes(&mut sk).unwrap());
            eq_keypairs(&kp1, &kp2) && sk == [0u8; 32]
        }
        QuickCheck::new().tests(10).quickcheck(prop as fn() -> _);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn sr25519_signature() {
        let kp = Keypair::generate();
        let pk = kp.public();

        let msg = "hello world".as_bytes();
        let sig = kp.sign(msg);
        assert!(pk.verify(msg, &sig));

        let mut invalid_sig = sig.clone();
        invalid_sig[3..6].copy_from_slice(&[10, 23, 42]);
        assert!(!pk.verify(msg, &invalid_sig));

        let invalid_msg = "h3ll0 w0rld".as_bytes();
        assert!(!pk.verify(invalid_msg, &sig));

        let mut unmarked_sig = sig.clone();
        unmarked_sig[63] &= !SIGNATURE_MARKER;
        assert!(!pk.verify(msg, &unmarked_sig));
    }

    #[test]
    fn verifies_a_schnorrkel_signature() {
        let kp = schnorrkel_keypair(1);
        let msg = b"hello world";
        let sig = kp.sign(signing_context(SIGNING_CONTEXT).bytes(msg));

        let pk = PublicKey::try_from_bytes(&kp.public.to_bytes()).unwrap();
        assert!(pk.verify(msg, &sig.to_bytes()));
        assert!(!pk.verify_in(b"another-context", msg, &sig.to_bytes()));
    }

    #[test]
    #[cfg(feature = "rand")]
    fn schnorrkel_verifies_a_signature() {
        let kp = Keypair::generate();
        let msg = b"hello world";
        let sig = kp.sign(msg);

        let pk = schnorrkel::PublicKey::from_bytes(&kp.public().to_bytes()).unwrap();
        let sig = schnorrkel::Signature::from_bytes(&sig).unwrap();
        pk.verify(signing_context(SIGNING_CONTEXT).bytes(msg), &sig)
            .unwrap();
    }

    #[test]
    fn public_key_is_the_scalar_times_the_basepoint() {
        let kp = schnorrkel_keypair(2);
        let mut sk = kp.secret.to_bytes()[..32].to_vec();
        let ours = Keypair::try_from_bytes(&mut sk).unwrap();

        assert_eq!(ours.public().to_bytes(), kp.public.to_bytes());
    }

    /// A signature from `@scure/sr25519` 2.4.0, an implementation independent of schnorrkel,
    /// under the `substrate` context: seed `0x42..0x61`, signing randomness `[7; 32]`, over the 64
    /// bytes `0..64`.
    #[test]
    fn verifies_a_scure_sr25519_signature() {
        let pk = PublicKey::try_from_bytes(&hex_literal::hex!(
            "ccddafdb8188e3edb0984780053ac7f357f1741c59292884d9fe3e5832d2f90f"
        ))
        .unwrap();
        let sig = hex_literal::hex!(
            "d8280e79fe66ee85d9f20cdbfccff261bbb7401140d098a54ec1b046bdfd670a"
            "50fa8e16adbe36b86fc1ac6e4c86921eae2817b5f86fdec12424d482077abc84"
        );
        let msg = (0..64).collect::<Vec<u8>>();

        assert!(pk.verify_in(b"substrate", &msg, &sig));
        assert!(!pk.verify(&msg, &sig));
    }

    #[test]
    fn the_identity_public_key_verifies_nothing() {
        let pk = PublicKey::try_from_bytes(&[0u8; 32]).unwrap();
        let mut sig = [0u8; 64];
        sig[..32].copy_from_slice(RistrettoPoint::mul_base(&Scalar::ONE).compress().as_bytes());
        sig[32..].copy_from_slice(Scalar::ONE.as_bytes());
        sig[63] |= SIGNATURE_MARKER;

        assert!(!pk.verify(b"hello world", &sig));
    }

    #[test]
    fn rejects_a_zero_or_non_canonical_secret_key() {
        assert!(SecretKey::try_from_bytes([0u8; 32]).is_err());
        assert!(SecretKey::try_from_bytes([0xffu8; 32]).is_err());
    }

    #[test]
    fn protobuf_encoding_is_the_key_type_and_compressed_point() {
        let pk = Keypair::from(SecretKey::try_from_bytes([1u8; 32]).unwrap()).public();
        let encoded = crate::PublicKey::from(pk.clone()).encode_protobuf();

        assert_eq!(&encoded[..4], &[0x08, 0x05, 0x12, 0x20]);
        assert_eq!(&encoded[4..], &pk.to_bytes());
        assert_eq!(
            crate::PublicKey::try_decode_protobuf(&encoded)
                .unwrap()
                .try_into_sr25519()
                .unwrap(),
            pk
        );
    }
}
