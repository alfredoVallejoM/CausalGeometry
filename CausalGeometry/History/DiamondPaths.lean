import CausalGeometry.History.PathEquivariance
import CausalGeometry.History.Trace

/-!
# Two actual paths around a concurrency diamond

These four declarations are relocated verbatim from
Variational/ElementaryEulerLagrange. Their historical namespace is preserved
so no consumer is forced through an alias or a migration. No variational
structure is needed to construct these paths.
-/
namespace CausalGeometry

universe u v
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalVariational

/-- The e-then-f two-step path around one genuine concurrency diamond. -/
def diamondPathEF
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    CausalPath S C d.afterEF :=
  .step e d.concurrent.1
    (.step f
      (S.concurrent_enabled_after_left d.concurrent)
      (.nil d.afterEF))

/-- The f-then-e path with its terminal configuration transported to the
canonical e-then-f endpoint using flatness of the concurrency diamond. -/
def diamondPathFE
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    CausalPath S C d.afterEF :=
  (CausalPath.step f d.concurrent.2.1
    (CausalPath.step e
      (S.concurrent_enabled_after_right d.concurrent)
      (CausalPath.nil d.afterFE))).castEnd
        (ConcurrencyDiamond.endpoint_eq d).symm

@[simp] theorem diamondPathEF_length
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (diamondPathEF d).length = 2 :=
  rfl

@[simp] theorem diamondPathFE_length
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (diamondPathFE d).length = 2 := by
  unfold diamondPathFE
  cases (ConcurrencyDiamond.endpoint_eq d)
  rfl

end CausalVariational
end CausalGeometry
