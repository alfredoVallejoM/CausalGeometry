import CausalGeometry.Number.FactorizationConvolution
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace CausalGeometry

namespace NatMobiusRegression

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Classical Mobius is the Dirichlet-convolution inverse of classical zeta. -/
theorem moebius_mul_zeta :
    (μ * ζ : ArithmeticFunction ℤ) = 1 :=
  ArithmeticFunction.moebius_mul_coe_zeta

/-- The reverse convolution identity also holds. -/
theorem zeta_mul_moebius :
    (ζ * μ : ArithmeticFunction ℤ) = 1 :=
  ArithmeticFunction.coe_zeta_mul_moebius

/-- Classical Mobius inversion, exposed as the regression target for the
causal incidence construction. -/
theorem inversion
    {f g : ℕ → ℤ} :
    (∀ n > 0, ∑ d ∈ n.divisors, f d = g n) ↔
      ∀ n > 0,
        ∑ ab ∈ n.divisorsAntidiagonal,
          μ ab.1 * g ab.2 = f n := by
  exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq

/-- Dirichlet multiplication is exactly the natural-number realization of the
generic factorization convolution. -/
theorem dirichlet_is_factorization_convolution
    (f g : ArithmeticFunction ℤ) (n : ℕ) :
    (f * g) n =
      FactorizationConvolution.natSystem.convolution f g n := by
  exact
    (FactorizationConvolution.nat_convolution_eq_dirichlet
      f g n).symm

end NatMobiusRegression
end CausalGeometry
