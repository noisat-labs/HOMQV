#![feature(non_exhaustive)]

#[macro_use] extern crate failure;
extern crate rand;
extern crate sha3;
extern crate digest;
extern crate subtle;
extern crate curve25519_dalek;

use rand::{ RngCore, CryptoRng };
use sha3::{ Sha3_256, Shake256 };
use digest::{ Input, FixedOutput, ExtendableOutput, XofReader };
use subtle::ConstantTimeEq;
use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::scalar::Scalar;


macro_rules! decompress {
    ( $e:expr ) => {
        match $e.decompress() {
            Some(e) => e,
            None => return Err(Error::Decompress)
        }
    }
}

macro_rules! check {
    ( $e:expr ) => {
        if $e.ct_eq(&[0; 32]).unwrap_u8() != 1 {
            $e
        } else {
            return Err(Error::Zero)
        }
    }
}


pub const SECRET_LENGTH: usize = 32;
pub const PUBLIC_LENGTH: usize = 32;
pub const MESSAGE_LENGTH: usize = 32;

pub struct SecretKey(Scalar);
pub struct PublicKey(CompressedEdwardsY);
pub struct Message(CompressedEdwardsY);

pub struct And<A, B>(pub A, pub B);
pub type Send<'a> = And<And<&'a str, &'a SecretKey>, And<&'a str, &'a PublicKey>>;
pub type Recv<'a> = And<And<&'a str, &'a PublicKey>, And<&'a str, &'a SecretKey>>;

#[derive(Debug, Fail)]
#[non_exhaustive]
#[must_use]
pub enum Error {
    #[fail(display = "EdwardsPoint decompress error")]
    Decompress,

    #[fail(display = "Not allow zero value")]
    Zero,

    #[fail(display = "Invalid length")]
    Length
}

impl SecretKey {
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> SecretKey {
        SecretKey(Scalar::random(rng))
    }

    pub fn as_bytes(&self) -> &[u8; SECRET_LENGTH] {
        self.0.as_bytes()
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<SecretKey, Error> {
        if bytes.len() >= SECRET_LENGTH {
            let mut sk = [0; SECRET_LENGTH];
            sk.copy_from_slice(check!(&bytes[..SECRET_LENGTH]));
            Ok(SecretKey(Scalar::from_bits(sk)))
        } else {
            Err(Error::Length)
        }
    }
}

impl PublicKey {
    pub fn from_secret(SecretKey(sk): &SecretKey) -> PublicKey {
        PublicKey((sk * &ED25519_BASEPOINT_TABLE).compress())
    }

    pub fn as_bytes(&self) -> &[u8; PUBLIC_LENGTH] {
        self.0.as_bytes()
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<PublicKey, Error> {
        if bytes.len() >= PUBLIC_LENGTH {
            let mut pk = [0; PUBLIC_LENGTH];
            pk.copy_from_slice(check!(&bytes[..PUBLIC_LENGTH]));
            Ok(PublicKey(CompressedEdwardsY(pk)))
        } else {
            Err(Error::Length)
        }
    }
}

impl Message {
    pub fn as_bytes(&self) -> &[u8; MESSAGE_LENGTH] {
        self.0.as_bytes()
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Message, Error> {
        if bytes.len() >= MESSAGE_LENGTH {
            let mut msg = [0; MESSAGE_LENGTH];
            msg.copy_from_slice(check!(&bytes[..MESSAGE_LENGTH]));
            Ok(Message(CompressedEdwardsY(msg)))
        } else {
            Err(Error::Length)
        }
    }
}

impl<'a> And<&'a str, &'a SecretKey> {
    pub fn send(self, (id, pk): (&'a str, &'a PublicKey)) -> Send<'a> {
        And(self, And(id, pk))
    }

    pub fn recv(self, (id, pk): (&'a str, &'a PublicKey)) -> Recv<'a> {
        And(And(id, pk), self)
    }
}

impl<'a> Send<'a> {
    pub fn agree<R: RngCore + CryptoRng>(&self, rng: &mut R, shared: &mut [u8]) -> Result<Message, Error> {
        let And(And(sender, SecretKey(sk)), And(receiver, PublicKey(pk))) = self;
        let pk = decompress!(pk);

        let y = Scalar::random(rng);
        let yy = (&y * &ED25519_BASEPOINT_TABLE).compress();

        let e = generate_e(yy.as_bytes(), receiver.as_bytes());

        let output = pk * (y + sk * e);

        let mut hasher = Shake256::default();
        hasher.process(output.compress().as_bytes());
        hasher.process(sender.as_bytes());
        hasher.process(receiver.as_bytes());
        hasher.process(yy.as_bytes());
        hasher.xof_result().read(shared);

        Ok(Message(yy))
    }
}

impl<'a> Recv<'a> {
    pub fn agree(&self, msg: &Message, shared: &mut [u8]) -> Result<(), Error> {
        let And(And(sender, PublicKey(pk)), And(receiver, SecretKey(sk))) = self;
        let Message(yy) = msg;
        let pk = decompress!(pk);
        let yy2 = decompress!(yy);

        let e = generate_e(yy.as_bytes(), receiver.as_bytes());

        let output = (yy2 + pk * e) * sk;

        let mut hasher = Shake256::default();
        hasher.process(output.compress().as_bytes());
        hasher.process(sender.as_bytes());
        hasher.process(receiver.as_bytes());
        hasher.process(yy.as_bytes());
        hasher.xof_result().read(shared);

        Ok(())
    }
}

#[inline]
fn generate_e(yy: &[u8], r: &[u8]) -> Scalar {
    let mut hasher = Sha3_256::default();
    let mut e = [0; 64];
    hasher.process(yy);
    hasher.process(r);
    e[..32].copy_from_slice(hasher.fixed_result().as_slice());
    Scalar::from_bytes_mod_order_wide(&e)
}


#[test]
fn test_homqv() {
    use rand::thread_rng;

    let mut rng = thread_rng();

    let address1 = "alice@homqv.ene";
    let sk1 = SecretKey::generate(&mut rng);
    let pk1 = PublicKey::from_secret(&sk1);
    let mut shared1 = [0; 32];

    let address2 = "bob@homqv.ene";
    let sk2 = SecretKey::generate(&mut rng);
    let pk2 = PublicKey::from_secret(&sk2);
    let mut shared2 = [0; 32];

    let msg = And(address1, &sk1).send((address2, &pk2))
        .agree(&mut rng, &mut shared1).unwrap();
    And(address2, &sk2).recv((address1, &pk1))
        .agree(&msg, &mut shared2).unwrap();

    assert_ne!(shared1, [0; 32]);
    assert_eq!(shared1, shared2);
}

#[test]
fn test_zero_msg() {
    assert!(Message::from_bytes(&[0; 32]).is_err());
}
