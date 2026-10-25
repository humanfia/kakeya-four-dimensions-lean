/-
Adapted from: here:o265
Original proofs by LOT session x0943, commit e0bf23d4b, file
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ClockIsotropicCensus.lean.
Packaged and independently checked by x1027.
-/
-- Original generic support bridge developed in this LOT tree, o265/x0943, ClockIsotropicCensus.lean.
import Submission.Lib.K4ParentSignalPreparation.Census
import Submission.Lib.K4SharpAffineSupport

set_option autoImplicit false

namespace Submission.Lib.K4ClockIsotropicSupport
open Set
open Submission.Lib.K4ParentSignalPreparation.Census
noncomputable section

/-- Coarsen only the base part of a product grid label. -/
def coarsenProductBase (steps : ℕ) (q : (Fin 3 → ℤ) × ℤ) : (Fin 3 → ℤ) × ℤ :=
  ((fun j => q.1 j/(2:ℤ)^steps),q.2)

theorem product_gridCode_dyadic_base {Ω : Type*} (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    (base hidden : ℝ) (steps : ℕ) (x : Ω) :
    gridCode z X (base*(2:ℝ)^steps) hidden x =
      coarsenProductBase steps (gridCode z X base hidden x) := by
  unfold gridCode coarsenProductBase
  congr 1
  funext j
  rw [div_mul_eq_div_div,Submission.Lib.K4XInterface.floor_div_two_pow]

/-- A physical P/a census yields an isotropic census for P/h at a
COARSER mesh. The base mesh floor is respected: its fine mesh is still
exactly epsilon, and only the output base code is coarsened. The count
pays powers of the envelope, without an inverse a/h factor. -/
theorem clock_isotropic_support_from_joint_census {Ω : Type*}
    (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {ε θ K d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : ε*(2:ℝ)^steps ≤ θ) :
    let mesh := ε*(2:ℝ)^steps
    ∃ S : Finset ((Fin 3 → ℤ) × ℤ),
      (S.card : ℝ)*mesh^((3:ℝ)+d) ≤ K^2*((2:ℝ)^steps)^3 ∧
      ∀ x∈E, gridCode z (fun x => θ*X x) mesh mesh x∈S := by
  classical
  let mesh := ε*(2:ℝ)^steps
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hKpow : K ≤ K^(100:ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : (1:ℕ) ≤ 100)
  have hKD : K ≤ (2:ℝ)^steps := hKpow.trans hsteps
  have hθD : θ ≤ (2:ℝ)^steps := hθK.trans hKD
  obtain ⟨hfinite,hcount⟩ := rescale_census_envelope E z X hε hθ hK hθK hd0 hd1 hcensus
    (p:=ε) (w:=mesh) le_rfl hε1
    (by dsimp [mesh]; nlinarith) hresolved (by dsimp [mesh]; nlinarith)
  let F := hfinite.toFinset
  let S := F.image (coarsenProductBase steps)
  have hcard : (S.card : ℝ) ≤ K^2/(ε^3*mesh^d) := by
    apply (show (S.card : ℝ) ≤ (F.card : ℝ) from by exact_mod_cast Finset.card_image_le).trans
    change (hfinite.toFinset.card : ℝ) ≤ _
    rw [←Set.ncard_eq_toFinset_card _ hfinite]
    exact hcount
  have hmeshD : 0 < mesh^d := Real.rpow_pos_of_pos hmesh d
  refine ⟨S,?_,?_⟩
  · calc
      _ = (S.card : ℝ)*mesh^3*mesh^d := by rw [Real.rpow_add hmesh]; norm_num; ring
      _ ≤ (K^2/(ε^3*mesh^d))*mesh^3*mesh^d := by gcongr
      _ = K^2*((2:ℝ)^steps)^3 := by
        have hs : mesh^3=ε^3*((2:ℝ)^steps)^3 := by dsimp [mesh]; ring
        rw [hs]
        field_simp
  · intro x hx
    have hh : gridCode z (fun x => θ*X x) ε mesh x∈F :=
      hfinite.mem_toFinset.mpr ⟨x,hx,rfl⟩
    rw [product_gridCode_dyadic_base]
    exact Finset.mem_image_of_mem _ hh

/-- Fixed polynomial coarsening fits in the clock-height range when the
input precision has its displayed envelope margin. -/
theorem exists_clock_coarsening_steps {ε θ K ζ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hK : 1 ≤ K)
    (hεζ : ε ≤ θ*ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1) :
    ∃ steps : ℕ, K^(100:ℕ) ≤ (2:ℝ)^steps ∧
      (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧ ε*(2:ℝ)^steps ≤ θ := by
  obtain ⟨n,hn,hup⟩ := exists_nat_pow_near (one_le_pow₀ hK) (by norm_num : (1:ℝ) < 2)
  let steps := n+1
  have hlo : K^(100:ℕ) ≤ (2:ℝ)^steps := hup.le
  have hhi : (2:ℝ)^steps ≤ 2*K^(100:ℕ) := by
    dsimp [steps]
    rw [pow_succ]
    nlinarith only [hn]
  refine ⟨steps,hlo,hhi,?_⟩
  have hθζ : 0 ≤ θ*ζ := hε.le.trans hεζ
  calc
    _ ≤ (θ*ζ)*(2:ℝ)^steps := mul_le_mul_of_nonneg_right hεζ (by positivity)
    _ ≤ (θ*ζ)*(2*K^(100:ℕ)) := mul_le_mul_of_nonneg_left hhi hθζ
    _ = θ*(2*K^(100:ℕ)*ζ) := by ring
    _ ≤ θ*1 := mul_le_mul_of_nonneg_left hmargin hθ.le
    _ = θ := mul_one _

/-- A clock-normalized isotropic support with one fixed envelope power.
The precision margin, mesh floors and exact coarsening ratio are explicit. -/
theorem clock_isotropic_support_with_precision_margin {Ω : Type*}
    (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {ε θ K d ζ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hεζ : ε ≤ θ*ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d)) :
    ∃ (steps : ℕ) (S : Finset ((Fin 3 → ℤ) × ℤ)),
      K^(100:ℕ) ≤ (2:ℝ)^steps ∧ (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧
      ε ≤ ε*(2:ℝ)^steps ∧ ε*(2:ℝ)^steps ≤ θ ∧
      (S.card : ℝ)*(ε*(2:ℝ)^steps)^((3:ℝ)+d) ≤ 8*K^(302:ℕ) ∧
      ∀ x∈E, gridCode z (fun x => θ*X x) (ε*(2:ℝ)^steps) (ε*(2:ℝ)^steps) x∈S := by
  obtain ⟨steps,hlo,hhi,hres⟩ := exists_clock_coarsening_steps hε hθ hK hεζ hmargin
  obtain ⟨S,hS,hcover⟩ := clock_isotropic_support_from_joint_census E z X hε hε1 hθ hK
    hθK hd0 hd1 hcensus steps hlo hres
  refine ⟨steps,S,hlo,hhi,?_,hres,hS.trans ?_,hcover⟩
  · exact le_mul_of_one_le_right hε.le ((one_le_pow₀ hK).trans hlo)
  · calc
      _ ≤ K^2*(2*K^(100:ℕ))^3 := by gcongr
      _ = 8*K^(302:ℕ) := by ring

end
end Submission.Lib.K4ClockIsotropicSupport
