-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/CoarseProfiles.lean.
-- Adapted within this LOT tree from o040, session x0115, commit 561995983838,
-- Submission/Obl/k4_matching_refinement_exponent/CoarseProfiles.lean. Existing provenance comments below are preserved.
import Submission.Obl.k4_matching_switching_target_certificate.CoarseNeighbors

open Set

namespace Submission.Obl.k4_matching_switching_target_certificate

open Submission.Obl.k4_matching_homogeneous_records (dyadicCenter)

/-- All time-cell coordinates in a coarse history. -/
noncomputable def coarseTimeProfile {n₁ n₂ : ℕ} (h : ℕ → ℕ) (k : ℕ)
    (x : (Fin n₁ × Fin n₂) × ℝ) : Fin (k + 1) → ℤ :=
  fun v => Int.floor (x.2 * (2 : ℝ) ^ h v)

/-- Both arms' jet bins at every level of a coarse history. -/
noncomputable def coarseBinProfile {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J : ℕ)
    (x : (Fin n₁ × Fin n₂) × ℝ) : Fin 2 → (Fin (k + 1) × Fin (J + 1)) → ℤ :=
  fun a vj => if a = 0 then
    Int.floor (w vj.1 vj.2 * iteratedDeriv vj.2 (f₁ x.1.1) (dyadicCenter (h vj.1) x.2))
  else
    Int.floor (w vj.1 vj.2 * iteratedDeriv vj.2 (f₂ x.1.2) (dyadicCenter (h vj.1) x.2))

/-- The finite profiles express precisely the history equality in the frozen
record certificate. -/
theorem coarse_profiles_eq_iff {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J : ℕ)
    (x y : (Fin n₁ × Fin n₂) × ℝ) :
    (coarseTimeProfile h k x = coarseTimeProfile h k y ∧
      coarseBinProfile f₁ f₂ h w k J x = coarseBinProfile f₁ f₂ h w k J y) ↔
      ∀ v : ℕ, v ≤ k →
        Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧
        ∀ j : ℕ, j ≤ J →
          Int.floor (w v j * iteratedDeriv j (f₁ x.1.1) (dyadicCenter (h v) x.2)) =
            Int.floor (w v j * iteratedDeriv j (f₁ y.1.1) (dyadicCenter (h v) y.2)) ∧
          Int.floor (w v j * iteratedDeriv j (f₂ x.1.2) (dyadicCenter (h v) x.2)) =
            Int.floor (w v j * iteratedDeriv j (f₂ y.1.2) (dyadicCenter (h v) y.2)) := by
  constructor
  · rintro ⟨ht, hb⟩ v hv
    refine ⟨congrFun ht ⟨v, by omega⟩, ?_⟩
    intro j hj
    constructor
    · have hh := congrArg (fun b : Fin 2 → (Fin (k + 1) × Fin (J + 1)) → ℤ =>
        b 0 (⟨v, by omega⟩, ⟨j, by omega⟩)) hb
      simpa [coarseBinProfile] using hh
    · have hh := congrArg (fun b : Fin 2 → (Fin (k + 1) × Fin (J + 1)) → ℤ =>
        b 1 (⟨v, by omega⟩, ⟨j, by omega⟩)) hb
      simpa [coarseBinProfile] using hh
  · intro heq
    constructor
    · funext v
      exact (heq v (Nat.le_of_lt_succ v.isLt)).1
    · funext a vj
      have hh := (heq vj.1 (Nat.le_of_lt_succ vj.1.isLt)).2
        vj.2 (Nat.le_of_lt_succ vj.2.isLt)
      fin_cases a
      · simpa [coarseBinProfile] using hh.1
      · simpa [coarseBinProfile] using hh.2

/-- A traversal fixes the entire earlier time-cell profile and the chosen
arm's earlier jet-bin profile. No regularity assumption is needed here. -/
theorem traversal_preserves_coarse_profile {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J : ℕ)
    (hh : ∀ v, v ≤ k → h v ≤ h k)
    (x y : (Fin n₁ × Fin n₂) × ℝ)
    (ht : Int.floor (x.2 * (2 : ℝ) ^ h k) = Int.floor (y.2 * (2 : ℝ) ^ h k))
    (harm : x.1.1 = y.1.1 ∨ x.1.2 = y.1.2) :
    coarseTimeProfile h k x = coarseTimeProfile h k y ∧
      ∃ a, coarseBinProfile f₁ f₂ h w k J x a = coarseBinProfile f₁ f₂ h w k J y a := by
  have hv : ∀ v, v ≤ k → Int.floor (x.2 * (2 : ℝ) ^ h v) =
      Int.floor (y.2 * (2 : ℝ) ^ h v) := fun v hv =>
    Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_eq_of_finer_eq (hh v hv) ht
  have hc : ∀ v, v ≤ k → dyadicCenter (h v) x.2 = dyadicCenter (h v) y.2 := by
    intro v hv'
    simp only [dyadicCenter, hv v hv']
  refine ⟨funext (fun v => hv v (Nat.le_of_lt_succ v.isLt)), ?_⟩
  rcases harm with harm | harm
  · refine ⟨0, ?_⟩
    funext vj
    simp only [coarseBinProfile, ite_true]
    rw [harm, hc vj.1 (Nat.le_of_lt_succ vj.1.isLt)]
  · refine ⟨1, ?_⟩
    funext vj
    simp only [coarseBinProfile, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    rw [harm, hc vj.1 (Nat.le_of_lt_succ vj.1.isLt)]

/-- Restricting equal fine histories to a coarser level preserves both
profiles. In particular every exact fine-record refresh is an allowed link. -/
theorem coarse_profiles_eq_of_finer {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k b J : ℕ) (hkb : k ≤ b)
    (x y : (Fin n₁ × Fin n₂) × ℝ)
    (heq : coarseTimeProfile h b x = coarseTimeProfile h b y ∧
      coarseBinProfile f₁ f₂ h w b J x = coarseBinProfile f₁ f₂ h w b J y) :
    coarseTimeProfile h k x = coarseTimeProfile h k y ∧
      coarseBinProfile f₁ f₂ h w k J x = coarseBinProfile f₁ f₂ h w k J y := by
  apply (coarse_profiles_eq_iff f₁ f₂ h w k J x y).mpr
  intro v hv
  exact (coarse_profiles_eq_iff f₁ f₂ h w b J x y).mp heq v (hv.trans hkb)

/-- The start-dependent family containing every coarse neighbor reached by
a bounded number of traversals. -/
def coarseNeighborBox {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J : ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (x₀ : (Fin n₁ × Fin n₂) × ℝ) (G : ℕ) :
    Set ((Fin n₁ × Fin n₂) × ℝ) :=
  {x | x ∈ S ∧ coarseTimeProfile h k x = coarseTimeProfile h k x₀ ∧
    ∀ a i, |coarseBinProfile f₁ f₂ h w k J x a i -
      coarseBinProfile f₁ f₂ h w k J x₀ a i| ≤ (G : ℤ)}

/-- The number of start-dependent coarse records is bounded independently
of the number of arms, time cells, and events. -/
theorem coarse_neighbor_record_count {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J : ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (F : ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (hF : ∀ x ∈ S, ∀ y ∈ S,
      coarseTimeProfile h k x = coarseTimeProfile h k y →
      coarseBinProfile f₁ f₂ h w k J x = coarseBinProfile f₁ f₂ h w k J y → F x = F y)
    (x₀ : (Fin n₁ × Fin n₂) × ℝ) (G : ℕ) :
    (F '' coarseNeighborBox f₁ f₂ h w k J S x₀ G).Finite ∧
      (F '' coarseNeighborBox f₁ f₂ h w k J S x₀ G).ncard ≤
        (2 * G + 1) ^ (2 * (k + 1) * (J + 1)) := by
  simpa only [coarseNeighborBox, Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using
    coarse_record_box_count S (coarseTimeProfile h k) (coarseBinProfile f₁ f₂ h w k J)
      F hF x₀ G

/-- Every allowed coarse-profile walk stays in the same polynomial-size
neighbor box. Equal fine-record refreshes are allowed by
`coarse_profiles_eq_of_finer`; arm traversals are allowed by
`traversal_preserves_coarse_profile`. -/
theorem coarse_walk_mem_neighbor_box {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J G n : ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (x : ℕ → (Fin n₁ × Fin n₂) × ℝ)
    (hx : ∀ p, p ≤ n → x p ∈ S)
    (hgap : ∀ y ∈ S, ∀ i,
      |coarseBinProfile f₁ f₂ h w k J y 0 i -
        coarseBinProfile f₁ f₂ h w k J y 1 i| ≤ (G : ℤ))
    (hstep : ∀ p, p < n →
      coarseTimeProfile h k (x p) = coarseTimeProfile h k (x (p + 1)) ∧
      ∃ a, coarseBinProfile f₁ f₂ h w k J (x p) a =
        coarseBinProfile f₁ f₂ h w k J (x (p + 1)) a) :
    x n ∈ coarseNeighborBox f₁ f₂ h w k J S (x 0) (2 * n * G) := by
  exact ⟨hx n le_rfl, bin_walk_bound S (coarseTimeProfile h k)
    (coarseBinProfile f₁ f₂ h w k J) G n x hx hgap hstep⟩

/-- All arms met by the walk remain close, at the common recorded centers,
to the first starting arm. This is the common Taylor-frame hypothesis of
the normalized endpoint comparison. -/
theorem coarse_walk_center_jet_bound {n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (h : ℕ → ℕ) (w : ℕ → ℕ → ℝ) (k J G n : ℕ)
    (hw : ∀ v, v ≤ k → ∀ j, j ≤ J → 0 < w v j)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (x : ℕ → (Fin n₁ × Fin n₂) × ℝ)
    (hx : ∀ p, p ≤ n → x p ∈ S)
    (hgap : ∀ y ∈ S, ∀ i,
      |coarseBinProfile f₁ f₂ h w k J y 0 i -
        coarseBinProfile f₁ f₂ h w k J y 1 i| ≤ (G : ℤ))
    (hstep : ∀ p, p < n →
      coarseTimeProfile h k (x p) = coarseTimeProfile h k (x (p + 1)) ∧
      ∃ a, coarseBinProfile f₁ f₂ h w k J (x p) a =
        coarseBinProfile f₁ f₂ h w k J (x (p + 1)) a) :
    ∀ a : Fin 2, ∀ v, v ≤ k → ∀ j, j ≤ J →
      |(if a = 0 then iteratedDeriv j (f₁ (x n).1.1) (dyadicCenter (h v) (x 0).2)
          else iteratedDeriv j (f₂ (x n).1.2) (dyadicCenter (h v) (x 0).2)) -
        iteratedDeriv j (f₁ (x 0).1.1) (dyadicCenter (h v) (x 0).2)| ≤
          ((((2 * n + 1) * G : ℕ) : ℝ) + 1) / w v j := by
  intro a v hv j hj
  have ht := (bin_walk_bound S (coarseTimeProfile h k)
    (coarseBinProfile f₁ f₂ h w k J) G n x hx hgap hstep).1
  have htv := congrFun ht (⟨v, by omega⟩ : Fin (k + 1))
  have hc : dyadicCenter (h v) (x n).2 = dyadicCenter (h v) (x 0).2 := by
    simp only [coarseTimeProfile] at htv
    simp only [dyadicCenter, htv]
  have hb := bin_walk_first_color_bound S (coarseTimeProfile h k)
    (coarseBinProfile f₁ f₂ h w k J) G n x hx hgap hstep a
      ((⟨v, by omega⟩ : Fin (k + 1)), (⟨j, by omega⟩ : Fin (J + 1)))
  have hr : |(coarseBinProfile f₁ f₂ h w k J (x n) a
        (⟨v, by omega⟩, ⟨j, by omega⟩) : ℝ) -
      (coarseBinProfile f₁ f₂ h w k J (x 0) 0 (⟨v, by omega⟩, ⟨j, by omega⟩) : ℝ)| ≤
        (((2 * n + 1) * G : ℕ) : ℝ) := by exact_mod_cast hb
  by_cases ha : a = 0
  · simp only [coarseBinProfile, ha, ite_true, hc] at hr
    simpa only [ha, ite_true] using real_gap_of_floor_gap (hw v hv j hj) hr
  · simp only [coarseBinProfile, ha, ite_false, ite_true, hc] at hr
    simpa only [ha, ite_false] using real_gap_of_floor_gap (hw v hv j hj) hr

end Submission.Obl.k4_matching_switching_target_certificate
