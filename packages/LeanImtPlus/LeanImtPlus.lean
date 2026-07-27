import LeanImtPlus.Core
import LeanImtPlus.Hasher.Sha256
import LeanImtPlus.Tree

/-!
# LeanIMT+ tree and unified proofs

The core API is generic over `LeanImtPlus.Hasher`. This convenience root also
imports the pure-Lean `Sha256Spec` adapter, preserving a lightweight default.
The OpenSSL and Poseidon2 adapters remain explicit opt-in imports:

```lean
import LeanImtPlus.Hasher.Sha256Ffi
import LeanImtPlus.Hasher.Poseidon2
```
-/
