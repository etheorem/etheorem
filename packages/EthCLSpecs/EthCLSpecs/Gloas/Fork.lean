import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.Gloas.Fork`: the lineage declaration (load order row 0)

The whole cross-fork edge, in one module, and the only place Gloas names Fulu
outside the two sanctioned boundary files.

The **feeder import** above is what makes inheritance work at all: Fulu's
captures and its lineage entry live in environment extensions, and an
environment extension travels only through an `.olean` import. Without the
import the resolver would find nothing to replay. Decoupling means no `open` and
no qualified reference into Fulu, and never the physical import
(`SPEC_AUTHORING_MODEL.md` §8).

The **placement** is forced by elaboration order. `inherit` reads `lineageExt`
as it elaborates, and every capturing form reads it to work out which fork it is
filing under, so the `fork … from …` edge must already be in the environment
before any other Gloas module elaborates. That puts it at the first module of
the intra-fork import chain: `Gloas/Types.lean` imports this file, and every
other Gloas module reaches it from there, importing intra-fork only.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

fork Gloas from Fulu

end EthCLSpecs.Gloas
