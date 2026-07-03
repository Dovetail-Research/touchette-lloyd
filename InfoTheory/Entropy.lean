module

public import InfoTheory.PFR.ForMathlib.Entropy.Basic
public import InfoTheory.PFR.ForMathlib.Entropy.Measure
public import InfoTheory.PFR.ForMathlib.Entropy.Kernel.Basic
public import InfoTheory.PFR.ForMathlib.Entropy.Kernel.MutualInfo

/-!
# Entropy API facade

Single entry point for the Shannon-entropy development (currently vendored
from the PFR project — see `VENDORED.md`). Import this module, never
`InfoTheory.PFR.*` directly; when the material lands in Mathlib, only this
file's imports change.

Provides `measureEntropy` (`Hm[μ]`), `entropy` (`H[X ; μ]`), `condEntropy`
(`H[X | Y ; μ]`), `mutualInfo` (`I[X : Y ; μ]`), `condMutualInfo`
(`I[X : Y | Z ; μ]`), and their kernel analogues (`Hk[κ, μ]`, `Ik[κ, μ]`),
plus the pairing notation `⟨X, Y⟩` for functions.
-/
