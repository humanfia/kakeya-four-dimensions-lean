-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/NeighborhoodPalettes.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Lib.K4IncidenceWitnesses

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set

/-- Nearby physical points use a bounded number of actual old cells.
Their field palettes therefore give a concrete local palette on the
new observed grid, without any conditioning of the source law. -/
theorem exists_neighborhood_field_palettes {Ω J β : Type*} (d : ℕ)
    (A : Set Ω) (obs : Ω → J) (physical : Ω → Fin d → ℝ)
    (center : J → Fin d → ℝ) (label : Ω → β)
    (ε R K : ℝ) (hε : 0 < ε) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (L : (Fin d → ℤ) → Finset β) (hL : ∀ q, ((L q).card : ℝ) ≤ K)
    (hknown : ∀ ω ∈ A, label ω ∈ L (fun j => ⌊physical ω j/ε⌋))
    (hnear : ∀ ω ∈ A, ∀ j, |physical ω j-center (obs ω) j| ≤ R*ε) :
    ∃ F : J → Finset β, (∀ i, ((F i).card : ℝ) ≤ (4*R+11)^d*K) ∧
      ∀ ω ∈ A, label ω ∈ F (obs ω) := by
  classical
  let Off : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun _ => Finset.Icc (-⌈R+1⌉) ⌈R+1⌉)
  have hN : 0 ≤ ((⌈R+1⌉ : ℤ) : ℝ) := by linarith [Int.le_ceil (R+1)]
  have hdiam : ∀ p ∈ Off, ∀ q ∈ Off, ∀ j,
      |(p j : ℝ)-(q j : ℝ)| ≤ 2*((⌈R+1⌉ : ℤ) : ℝ) := by
    intro p hp q hq j
    have hpj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hp j)
    have hqj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq j)
    have hpL : -((⌈R+1⌉ : ℤ) : ℝ) ≤ (p j : ℝ) := by exact_mod_cast hpj.1
    have hpU : (p j : ℝ) ≤ ((⌈R+1⌉ : ℤ) : ℝ) := by exact_mod_cast hpj.2
    have hqL : -((⌈R+1⌉ : ℤ) : ℝ) ≤ (q j : ℝ) := by exact_mod_cast hqj.1
    have hqU : (q j : ℝ) ≤ ((⌈R+1⌉ : ℤ) : ℝ) := by exact_mod_cast hqj.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hOff : (Off.card : ℝ) ≤ (4*R+11)^d := by
    have hc := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter Off
      (by positivity : 0 ≤ 2*((⌈R+1⌉ : ℤ) : ℝ)) hdiam
    simp only [Fintype.card_fin] at hc
    apply hc.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith [Int.ceil_lt_add_one (R+1)]
  let F (i : J) := Off.biUnion fun δ => L (fun j => ⌊center i j/ε⌋+δ j)
  refine ⟨F,?_,?_⟩
  · intro i
    have hcard : ((F i).card : ℝ) ≤
        ∑ δ ∈ Off, ((L (fun j => ⌊center i j/ε⌋+δ j)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    calc
      _ ≤ ∑ _δ ∈ Off, K := hcard.trans (Finset.sum_le_sum fun δ _ => hL _)
      _ = (Off.card : ℝ)*K := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hOff hK
  · intro ω hω
    let δ : Fin d → ℤ := fun j => ⌊physical ω j/ε⌋-⌊center (obs ω) j/ε⌋
    have hδ : δ ∈ Off := Fintype.mem_piFinset.mpr fun j =>
      Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem hε (hnear ω hω j)
    apply Finset.mem_biUnion.mpr
    refine ⟨δ,hδ,?_⟩
    have heq : (fun j => ⌊center (obs ω) j/ε⌋+δ j)=(fun j => ⌊physical ω j/ε⌋) := by
      ext j
      dsimp only [δ]
      ring
    rw [heq]
    exact hknown ω hω

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
