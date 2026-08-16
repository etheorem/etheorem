import EthCLLib

/-!
# `EthCLSpecs.Fulu.Fork`: the lineage declaration (load order row 0)

One line of content, and it has to be alone in its own module. `inherit` reads
`lineageExt` while it elaborates, and a capturing form reads it to work out which
fork it is filing under, so the lineage edge must already be in the environment
before any *other* module of the fork elaborates. That forces the declaration to
the first module of the fork's intra-fork import chain, which is this one:
`Types.lean` imports it, and everything else reaches it from there.

The fork's library root (`EthCLSpecs/Fulu.lean`) cannot hold it. A root is a
re-export aggregator that imports the fork's modules, so it elaborates last, long
after the modules that need the edge.

Fulu is the base of the tree, so there is no `from` clause and no feeder import
of a parent library root. A child fork's `Fork.lean` carries both
(`SPEC_AUTHORING_MODEL.md` §8), and this file exists at a root fork for the
uniformity: "where is a fork's lineage declared" has one answer across the tree.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

fork Fulu

end EthCLSpecs.Fulu
