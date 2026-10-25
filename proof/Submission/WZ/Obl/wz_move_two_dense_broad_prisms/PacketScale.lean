-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PacketScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.AngularCount
import Submission.WZ.Obl.wz_broad_grains_initialization.MeasurablePackets

/-! A broad packet refinement with high incidence density cannot choose a tiny scale. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal
open wz_broad_grains_initialization (PacketRefinement)
open wz_clustered_cover_volume_gain (bodyCount body_mass_le_mul_of_count)

lemma packet_point_count {d θ β m : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 < θ) (hdθ : d ≤ 2 * θ) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hK : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ O m * μ W)
    (hR : PacketRefinement β d θ v Y Z F a) (p : V) :
    bodyCount Z p * d ^ 2 * θ ^ β ≤ 1728 * m * θ ^ 2 := by
  classical
  by_cases hnon : ∃ i, p ∈ Z i
  · obtain ⟨i, hi⟩ := hnon
    have hcover := (hR.2.2.2 p).2.1
    have hmem : i ∈ (F p).biUnion id := by
      change i ∈ ((F p).biUnion id : Set (Fin n))
      rw [hcover]
      exact hi
    obtain ⟨W, hWF, hiW⟩ := Finset.mem_biUnion.mp hmem
    have hW := (hR.2.2.2 p).2.2 W hWF
    have hWT : ∀ j ∈ W, p ∈ T d (x j) (v j) := by
      intro j hj
      have hjZ : p ∈ Z j := by
        change j ∈ {i | p ∈ Z i}
        rw [← hcover]
        exact Finset.mem_biUnion.mpr ⟨W, hWF, hj⟩
      exact hYT j ((hR.1 j).2 hjZ)
    have hWcount : (W.card : ℝ) ≤
        q n {j | p ∈ T d (x j) (v j) ∧ min ‖v j-v (a p W)‖ ‖v j+v (a p W)‖ ≤ 2 * θ} := by
      have hsub : (W : Set (Fin n)) ⊆
          {j | p ∈ T d (x j) (v j) ∧ min ‖v j-v (a p W)‖ ‖v j+v (a p W)‖ ≤ 2 * θ} :=
        fun j hj => ⟨hWT j hj, hW.2.1 j hj⟩
      have hh := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hh
      exact_mod_cast hh
    have hcap := point_cap_count hd hd1 hdθ hm hv hK p (v (a p W)) (hv _)
    have hbig : bodyCount Y p / 2 * θ ^ β ≤ W.card := hW.2.2.1
    have hmono : bodyCount Z p ≤ bodyCount Y p := by
      change (Set.ncard _ : ℝ) ≤ (Set.ncard _ : ℝ)
      exact_mod_cast Set.ncard_le_ncard (show {j | p ∈ Z j} ⊆ {j | p ∈ Y j} from
        fun j hj => (hR.1 j).2 hj)
    have h₁ := mul_le_mul_of_nonneg_right hWcount (sq_nonneg d)
    have h₂ := mul_le_mul_of_nonneg_right hbig (sq_nonneg d)
    have h₃ := mul_le_mul_of_nonneg_right hmono
      (show 0 ≤ d ^ 2 * θ ^ β by positivity)
    nlinarith
  · have he : {i | p ∈ Z i} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun i hi => hnon ⟨i, hi⟩)
    simp only [bodyCount, he, Set.ncard_empty, Nat.cast_zero, zero_mul]
    positivity

/-- The integrated packet bound preserves the entire retained incidence mass. -/
lemma packet_mass_bound {d θ β m : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n} {E : Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 < θ) (hdθ : d ≤ 2 * θ) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hK : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ O m * μ W)
    (hR : PacketRefinement β d θ v Y Z F a)
    (hE : MeasurableSet E) (hZE : ∀ i, Z i ⊆ E) :
    (∑ i, μ (Z i)) ≤ O (1728 * m / d ^ 2 * θ ^ (2-β)) * μ E := by
  have hcoef : 1728 * m / d ^ 2 * θ ^ (2-β) =
      1728 * m * θ ^ 2 / (d ^ 2 * θ ^ β) := by
    rw [Real.rpow_sub hθ, Real.rpow_two]
    ring
  have hC0 : 0 ≤ 1728 * m / d ^ 2 * θ ^ (2-β) := by positivity
  have hcount (p : V) : bodyCount Z p ≤
      (1728 * m / d ^ 2 * θ ^ (2-β)) * bodyCount (fun _ : Fin 1 => E) p := by
    by_cases hp : p ∈ E
    · have he : bodyCount (fun _ : Fin 1 => E) p = 1 := by simp [bodyCount, hp]
      rw [he, mul_one, hcoef]
      apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hd) (Real.rpow_pos_of_pos hθ β))).mpr
      simpa only [mul_assoc] using packet_point_count hd hd1 hθ hdθ hm hv hYT hK hR p
    · have he : {i | p ∈ Z i} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun i hi => hp (hZE i hi)
      simp only [bodyCount, he, Set.ncard_empty, Nat.cast_zero]
      positivity
  simpa only [Fin.sum_univ_one] using body_mass_le_mul_of_count
    (fun i => (hR.1 i).1) (fun _ : Fin 1 => hE) hC0 hcount

/-- High density in a finite positive-volume container gives a quantitative
lower bound for the chosen angular scale. -/
theorem packet_scale_lower {d θ β m D r : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {a : V → Finset (Fin n) → Fin n} {E : Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 < θ) (hdθ : d ≤ 2 * θ) (hm : 0 ≤ m)
    (hD : 0 ≤ D) (hβ : β ≤ 2)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (hK : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ O m * μ W)
    (hR : PacketRefinement β d θ v Y Z F a)
    (hE : MeasurableSet E) (hZE : ∀ i, Z i ⊆ E)
    (hE0 : μ E ≠ 0) (hEfin : μ E ≠ ∞)
    (hmass : O D * μ E ≤ ∑ i, μ (Z i))
    (hbudget : 1728 * m * r ^ (2-β) < D * d ^ 2) : r < θ := by
  have hbound := hmass.trans (packet_mass_bound hd hd1 hθ hdθ hm hv hYT hK hR hE hZE)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hvol : 0 < (μ E).toReal := ENNReal.toReal_pos hE0 hEfin
  have hDC : D ≤ 1728 * m / d ^ 2 * θ ^ (2-β) := by nlinarith
  have hDC' : D * d ^ 2 ≤ 1728 * m * θ ^ (2-β) := by
    calc
      _ ≤ (1728 * m / d ^ 2 * θ ^ (2-β)) * d ^ 2 :=
        mul_le_mul_of_nonneg_right hDC (sq_nonneg d)
      _ = _ := by field_simp
  by_contra hnot
  have hθr : θ ≤ r := le_of_not_gt hnot
  have hp : θ ^ (2-β) ≤ r ^ (2-β) := Real.rpow_le_rpow hθ.le hθr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1728*m by positivity)
  linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
