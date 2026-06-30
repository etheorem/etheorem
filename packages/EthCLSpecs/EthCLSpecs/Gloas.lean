import EthCLSpecs.Gloas.Containers
import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Gloas.Interface

/-!
# `EthCLSpecs.Gloas`: the Gloas fork (EIP-7732 ePBS), a diff over Fulu

`fork Gloas from Fulu` plus the ePBS + EIP-8282 container diff, the `upgradeToGloas`
lifecycle entry, and the fork-interface instance. Pinned to the v1.7.0-alpha.11
spec shape (the pyspec vectors' version). The transition spine, operations,
and fork choice are inherited from / diffed over Fulu as that port matures. The
EIP-8282 builder-deposit / builder-exit operation processing is deferred (xfail).
-/
