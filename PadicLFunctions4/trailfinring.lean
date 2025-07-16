import PadicLFunctions4.BerMeasBerMeasDef
import PadicLFunctions4.Teich
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

variable {p : ℕ} [Fact p.Prime]

noncomputable def bernoulli_distribution_copy (n : ℕ) (a : (ZMod (d * (p^n)))) :=
