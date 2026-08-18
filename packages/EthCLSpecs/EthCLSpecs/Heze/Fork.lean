import EthCLSpecs.Gloas

/-!
# `EthCLSpecs.Heze.Fork`: the lineage declaration (load order row 0)

The whole cross-fork edge, in one module, and the only place Heze names Gloas
outside the two sanctioned boundary files.

The **feeder import** above carries Gloas's captures and its own lineage entry:
those live in environment extensions, which travel only through an `.olean`
import. Decoupling means no `open` and no qualified reference into Gloas, and
never the physical import (`SPEC_AUTHORING_MODEL.md` §8). Fulu rides in
transitively, which is what lets a Heze `inherit` walk two generations up when
Gloas left a declaration unchanged.

The **placement** is forced by elaboration order: `inherit` and every capturing
form read `lineageExt` as they elaborate, so the edge must be in the environment
before any other Heze module elaborates. `Heze/Types.lean` imports this file;
every other Heze module reaches it from there, importing intra-fork only.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

fork Heze from Gloas

end EthCLSpecs.Heze
