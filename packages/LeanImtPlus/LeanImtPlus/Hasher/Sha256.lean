import LeanImtPlus.Hasher.Class
import LeanSha256

set_option autoImplicit false

/-!
# Pure SHA-256 LeanIMT+ adapter

This is the kernel-reducible implementation of the SHA-256 circuit encoding:
each input is a 216-bit big-endian integer, and each digest is truncated to its
low 216 bits.
-/

namespace LeanImtPlus

/-- Phantom tag selecting the pure-Lean SHA-256 implementation. -/
inductive Sha256Spec : Type

namespace Sha256

/-- Size of the SHA-256 LeanIMT+ digest domain. -/
def twoPow216 : Nat := 2 ^ 216

/-- Largest canonical SHA-256 LeanIMT+ digest. -/
def max216 : Nat := twoPow216 - 1

/-- Whether `n` fits the circuit's 216-bit input domain. -/
def fits216 (n : Nat) : Bool :=
  n < twoPow216

private def byteAtBE (width : Nat) (n : Nat) (i : Nat) : UInt8 :=
  Nat.toUInt8 ((n >>> (8 * (width - 1 - i))) &&& 0xff)

/-- Encode `n` as a fixed-width, big-endian byte string. -/
def toBytesBE (width : Nat) (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := width) fun i => byteAtBE width n i.val)

/-- Circuit input encoding: 216 bits as 27 big-endian bytes. -/
def toBE27 (n : Nat) : ByteArray :=
  toBytesBE 27 n

/-- Decode a big-endian byte string into a natural number. -/
def natFromBytesBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Extract the low 216 bits from a SHA-256 digest. -/
def low216FromDigest (digest : ByteArray) : Nat :=
  natFromBytesBE digest % twoPow216

/-- Apply a SHA-256 implementation to two circuit-encoded inputs. -/
def hash2With (hash : ByteArray → ByteArray) (left right : Nat) : Nat :=
  low216FromDigest (hash (toBE27 left ++ toBE27 right))

/-- Pure-Lean SHA-256 two-to-one operation. -/
def hash2 (left right : Nat) : Nat :=
  hash2With LeanSha256.hash left right

end Sha256

@[reducible] instance : Hasher Sha256Spec where
  Digest := Nat
  digestInhabited := inferInstance
  digestBEq := inferInstance
  digestRepr := inferInstance
  validValue := Sha256.fits216
  validDigest := Sha256.fits216
  ofNat := id
  compress := Sha256.hash2

end LeanImtPlus
