-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Compatibility.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.GroupGlue
import Submission.Obl.k4_clean_cover_graph_atlas.RegionGeometry
import Submission.Obl.k4_clean_cover_graph_atlas.CanonicalOldLists

/-!
# Observation domains of entry groups

The observation domain of a group `(Q, jj, k, st)` is the set of terminal observations whose base
time lies in the sub-block, whose normalized observed position lies within `(κ+1) 2^{-s₀}` of the box
centre, and at which `Q` is a canonical old chart (`groupObs`). It is measurable, contains the
observation of every incidence of the group's lines on the sub-block inside `F Q`, and one
observation meets at most `κ · 2 · (2κ+3)² · 2` groups of one world.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Submission.Lib.K4XInterface

/-- The normalized spatial coordinate of an observed base point in a chart frame. -/
noncomputable def zcObs (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![o.1 1, o.1 2] - c - o.1 0 • u)

theorem zcObs_obs (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Bv a : ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : zcObs Q c u (obs Bv a p) = zc Q c u p.1 p.2 := by
  unfold zcObs zc
  congr 2

theorem continuous_zcObs (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) :
    Continuous (zcObs Q c u) := by
  unfold zcObs
  refine (Matrix.toEuclideanLin Q⁻¹).continuous_of_finiteDimensional.comp ?_
  refine Continuous.sub (Continuous.sub ?_ continuous_const) ?_
  · refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun e => ?_
    fin_cases e
    · exact (continuous_apply (1 : Fin 3)).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
    · exact (continuous_apply (2 : Fin 3)).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
  · exact ((continuous_apply (0 : Fin 3)).comp
      ((PiLp.continuous_ofLp 2 _).comp continuous_fst)).smul continuous_const

/-- The observation domain of an entry group. -/
noncomputable def groupObs {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W) (B : Fin W → ℝ)
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Nk L : ℝ) (i : ℕ) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (Ti s₀ K : ℕ) (κ : ℝ) (G : Group C s₀ K) : Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  {o | G.1 ∈ canonicalOldLists lev γ B F Nk L i (γ G.1) o ∧
    o.1 0 ∈ subBlock Ti s₀ (j G.1) G.2.1 ∧
    ‖zcObs (Q G.1) (c G.1) (u G.1) o - boxCenter s₀ (boxOf K G.2.2.1)‖ ≤ side s₀ * (κ + 1)}

theorem measurableSet_groupObs {C W D : ℕ} {H : ℝ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (B : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hfmt : ∀ b q, fmt 7 H D {z : Fin 7 → ℝ | ((q, fun j => z j.castSucc), z 6) ∈ F b})
    (Nk L : ℝ) (i : ℕ) (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (Ti s₀ K : ℕ) (κ : ℝ) (G : Group C s₀ K) :
    MeasurableSet (groupObs lev γ B F Nk L i j c u Q Ti s₀ K κ G) := by
  refine (measurable_canonicalOldLists lev γ B F hfmt Nk L i (γ G.1) G.1).inter
    (MeasurableSet.inter ?_ ?_)
  · have hc : Continuous fun o : EuclideanSpace ℝ (Fin 3) × ℤ => o.1 0 :=
      (continuous_apply (0 : Fin 3)).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
    exact measurableSet_Icc.preimage hc.measurable
  · have hc : Continuous fun o : EuclideanSpace ℝ (Fin 3) × ℤ =>
        ‖zcObs (Q G.1) (c G.1) (u G.1) o - boxCenter s₀ (boxOf K G.2.2.1)‖ :=
      ((continuous_zcObs _ _ _).sub continuous_const).norm
    exact measurableSet_le hc.measurable measurable_const

/-- Incidences of a group's lines on its sub-block inside the old packet's incidence set observe
inside the group's observation domain. -/
theorem obs_mem_groupObs {Nk L : ℝ} {M D : ℕ} {κ : ℝ} {C W : ℕ} {lev : Fin C → ℕ}
    {γ : Fin C → Fin W} {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {i : ℕ} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
    {ex : Fin C → Prop} {rold : ℝ} {Ti : ℕ}
    {n : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {s₀ K : ℕ}
    (hold : ∀ a, gchart Nk M D κ Ti (j (old a) : ℝ) rold (B (γ (old a))) (E (γ (old a)))
      (c (old a)) (u (old a)) (Q (old a)) (R (old a)) (A (old a)) (F (old a)) (ex (old a)))
    (hlev : ∀ a, lev (old a) = i) (hA'A : ∀ a, A' a ⊆ A (old a))
    (e : Entry n s₀ K) {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hpF : p ∈ F (old e.1))
    (hpm : p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e)
    (hpt : p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1) :
    obs (B (γ (old e.1))) (δ Nk L) p ∈
      groupObs lev γ B F Nk L i j c u Q Ti s₀ K κ (entryGroup old e) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_canonicalOldLists lev γ B F Nk L i _ _ _).mpr ⟨hlev e.1, rfl, p, hpF, rfl⟩
  · exact hpt
  · change ‖zcObs (Q (old e.1)) (c (old e.1)) (u (old e.1)) (obs (B (γ (old e.1))) (δ Nk L) p) -
      boxCenter s₀ (boxOf K e.2.2.1)‖ ≤ side s₀ * (κ + 1)
    rw [zcObs_obs]
    obtain ⟨hA', hbox⟩ := memE_subset_inBox old R' A' j c u Q R Ti s₀ K hpm
    exact zc_near_boxCenter (hold e.1) (hA'A e.1 hA') hbox hpt

/-- At most `2r + 1` elements of `Fin M` lie within `r` of a real number. -/
theorem card_fin_near (M : ℕ) (x r : ℝ) (hr : 0 ≤ r) :
    ((Finset.univ.filter (fun k : Fin M => |(k : ℝ) - x| ≤ r)).card : ℝ) ≤ 2 * r + 1 := by
  classical
  set S := Finset.univ.filter (fun k : Fin M => |(k : ℝ) - x| ≤ r)
  -- inject into the integers of `[x - r, x + r]`
  let f : Fin M → ℤ := fun k => (k : ℤ)
  have hinj : Set.InjOn f S := by
    intro a _ b _ h
    exact Fin.ext (by simpa [f] using h)
  have hmaps : ∀ k ∈ S, f k ∈ Finset.Icc ⌈x - r⌉ ⌊x + r⌋ := by
    intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := abs_le.mp hk
    simp only [Finset.mem_Icc, f]
    constructor
    · rw [Int.ceil_le]; push_cast; linarith
    · rw [Int.le_floor]; push_cast; linarith
  have hcard : S.card ≤ (Finset.Icc ⌈x - r⌉ ⌊x + r⌋).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  rw [Int.card_Icc] at hcard
  have h1 : ((⌊x + r⌋ + 1 - ⌈x - r⌉).toNat : ℝ) ≤ 2 * r + 1 := by
    rcases le_or_gt (⌊x + r⌋ + 1 - ⌈x - r⌉) 0 with h | h
    · rw [Int.toNat_eq_zero.mpr h]; push_cast; linarith
    · have := Int.toNat_of_nonneg h.le
      have e : ((⌊x + r⌋ + 1 - ⌈x - r⌉).toNat : ℝ) = ((⌊x + r⌋ + 1 - ⌈x - r⌉ : ℤ) : ℝ) := by
        exact_mod_cast this
      rw [e]
      push_cast
      have := Int.floor_le (x + r)
      have := Int.le_ceil (x - r)
      linarith
  calc (S.card : ℝ) ≤ ((⌊x + r⌋ + 1 - ⌈x - r⌉).toNat : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * r + 1 := h1

open Classical in
/-- Sub-blocks containing a time: at most two. -/
theorem card_subblocks_le (Ti s₀ j₀ : ℕ) (t : ℝ) :
    ((Finset.univ.filter (fun jj : Fin (2 ^ s₀) => t ∈ subBlock Ti s₀ j₀ jj)).card : ℝ) ≤ 2 := by
  set X := (2 : ℝ) ^ (Ti + s₀) * t - (j₀ : ℝ) * 2 ^ s₀ - 1 / 2
  have hsub : Finset.univ.filter (fun jj : Fin (2 ^ s₀) => t ∈ subBlock Ti s₀ j₀ jj) ⊆
      Finset.univ.filter (fun jj : Fin (2 ^ s₀) => |((jj : ℕ) : ℝ) - X| ≤ 1 / 2) := by
    intro jj hjj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, subBlock, Set.mem_Icc] at hjj ⊢
    have h2 : (0 : ℝ) < 2 ^ (Ti + s₀) := by positivity
    obtain ⟨h1, h3⟩ := hjj
    rw [div_le_iff₀ h2] at h1
    rw [le_div_iff₀ h2] at h3
    simp only [subIdx] at h1 h3
    push_cast at h1 h3
    have hX : X = (2 : ℝ) ^ (Ti + s₀) * t - (j₀ : ℝ) * 2 ^ s₀ - 1 / 2 := rfl
    rw [abs_le, hX]
    constructor <;> nlinarith
  calc ((Finset.univ.filter (fun jj : Fin (2 ^ s₀) => t ∈ subBlock Ti s₀ j₀ jj)).card : ℝ)
      ≤ ((Finset.univ.filter (fun jj : Fin (2 ^ s₀) => |((jj : ℕ) : ℝ) - X| ≤ 1 / 2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 * (1 / 2) + 1 := card_fin_near _ X (1 / 2) (by norm_num)
    _ = 2 := by norm_num

open Classical in
/-- Boxes near an observed normalized position: at most `(2κ+3)²`. -/
theorem card_boxes_le (s₀ K : ℕ) (z : EuclideanSpace ℝ (Fin 2)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ((Finset.univ.filter (fun k : Fin 2 → Fin (2 * K + 2) =>
      ‖z - boxCenter s₀ (boxOf K k)‖ ≤ side s₀ * (κ + 1))).card : ℝ) ≤ (2 * κ + 3) ^ 2 := by
  have hs := side_pos s₀
  set X : Fin 2 → ℝ := fun e => z e / side s₀ - 1 / 2 + K + 1
  set S1 : Fin 2 → Finset (Fin (2 * K + 2)) := fun e =>
    Finset.univ.filter (fun k : Fin (2 * K + 2) => |((k : ℕ) : ℝ) - X e| ≤ κ + 1)
  have hsub : Finset.univ.filter (fun k : Fin 2 → Fin (2 * K + 2) =>
      ‖z - boxCenter s₀ (boxOf K k)‖ ≤ side s₀ * (κ + 1)) ⊆ Fintype.piFinset S1 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Fintype.mem_piFinset]
    intro e
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, X]
    have hc := (PiLp.norm_apply_le (z - boxCenter s₀ (boxOf K k)) e).trans hk
    rw [Real.norm_eq_abs] at hc
    simp only [PiLp.sub_apply, boxCenter, boxOf] at hc
    push_cast at hc
    have key : ((k e : ℕ) : ℝ) - (z e / side s₀ - 1 / 2 + K + 1) =
        -((z e - (((k e : ℝ) - (K + 1)) + 1 / 2) * side s₀) / side s₀) := by
      field_simp
      ring
    rw [key, abs_neg, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    simpa [mul_comm] using hc
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  have h1 : ∀ e, ((S1 e).card : ℝ) ≤ 2 * κ + 3 := by
    intro e
    have := card_fin_near (2 * K + 2) (X e) (κ + 1) (by linarith)
    linarith
  calc _ ≤ ((∏ e, (S1 e).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ∏ e, ((S1 e).card : ℝ) := by push_cast; rfl
    _ ≤ ∏ _e : Fin 2, (2 * κ + 3) := by
        rw [Fin.prod_univ_two, Fin.prod_univ_two]
        have a0 := h1 0
        have a1 := h1 1
        have b0 : (0 : ℝ) ≤ (S1 0).card := by positivity
        have b1 : (0 : ℝ) ≤ (S1 1).card := by positivity
        exact mul_le_mul a0 a1 b1 (by linarith)
    _ = (2 * κ + 3) ^ 2 := by rw [Fin.prod_univ_two]; ring

open Classical in
/-- **Groups met by one observation.** If at most `κ` old charts of the level are canonically met by
the observation, it meets at most `4 κ (2κ+3)²` groups of a world. -/
theorem card_groups_le {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W) (B : Fin W → ℝ)
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Nk L : ℝ) (i : ℕ) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (Ti s₀ K : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ)
    (hcanon : ((canonicalOldLists lev γ B F Nk L i w o).card : ℝ) ≤ κ) :
    ((Finset.univ.filter (fun G : Group C s₀ K =>
      γ G.1 = w ∧ o ∈ groupObs lev γ B F Nk L i j c u Q Ti s₀ K κ G)).card : ℝ) ≤
      4 * κ * (2 * κ + 3) ^ 2 := by
  set canon := canonicalOldLists lev γ B F Nk L i w o
  let JJ : Fin C → Finset (Fin (2 ^ s₀)) := fun b =>
    Finset.univ.filter (fun jj : Fin (2 ^ s₀) => o.1 0 ∈ subBlock Ti s₀ (j b) jj)
  let KK : Fin C → Finset (Fin 2 → Fin (2 * K + 2)) := fun b =>
    Finset.univ.filter (fun k : Fin 2 → Fin (2 * K + 2) =>
      ‖zcObs (Q b) (c b) (u b) o - boxCenter s₀ (boxOf K k)‖ ≤ side s₀ * (κ + 1))
  have hsub : Finset.univ.filter (fun G : Group C s₀ K =>
      γ G.1 = w ∧ o ∈ groupObs lev γ B F Nk L i j c u Q Ti s₀ K κ G) ⊆
      canon.biUnion (fun b => ((JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool))).image
        (fun x => (b, x))) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    obtain ⟨hw, hcan, ht, hz⟩ := hG
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    refine ⟨G.1, ?_, G.2, ⟨?_, ?_⟩, rfl⟩
    · show G.1 ∈ canonicalOldLists lev γ B F Nk L i w o
      rw [← hw]; exact hcan
    · simp only [JJ, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht
    · simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and]; exact hz
  have hJ : ∀ b, ((JJ b).card : ℝ) ≤ 2 := fun b => card_subblocks_le Ti s₀ (j b) (o.1 0)
  have hK : ∀ b, ((KK b).card : ℝ) ≤ (2 * κ + 3) ^ 2 :=
    fun b => card_boxes_le s₀ K (zcObs (Q b) (c b) (u b) o) hκ
  have hcard := Finset.card_le_card hsub
  have hb := Finset.card_biUnion_le (s := canon) (t := fun b => ((JJ b) ×ˢ ((KK b) ×ˢ
    (Finset.univ : Finset Bool))).image (fun x => (b, x)))
  have hterm : ∀ b, ((((JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool))).image
      (fun x => (b, x))).card : ℝ) ≤ 2 * (2 * κ + 3) ^ 2 * 2 := by
    intro b
    have h1 := Finset.card_image_le (s := (JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool)))
      (f := fun x => (b, x))
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool] at h1
    calc _ ≤ (((JJ b).card * ((KK b).card * 2) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((JJ b).card : ℝ) * (((KK b).card : ℝ) * 2) := by push_cast; ring
      _ ≤ 2 * ((2 * κ + 3) ^ 2 * 2) := by
          gcongr
          · exact hJ b
          · exact hK b
      _ = 2 * (2 * κ + 3) ^ 2 * 2 := by ring
  calc _ ≤ ((canon.biUnion (fun b => ((JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool))).image
        (fun x => (b, x)))).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((∑ b ∈ canon, (((JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool))).image
        (fun x => (b, x))).card : ℕ) : ℝ) := by exact_mod_cast hb
    _ = ∑ b ∈ canon, ((((JJ b) ×ˢ ((KK b) ×ˢ (Finset.univ : Finset Bool))).image
        (fun x => (b, x))).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _b ∈ canon, (2 * (2 * κ + 3) ^ 2 * 2) := Finset.sum_le_sum fun b _ => hterm b
    _ = (canon.card : ℝ) * (2 * (2 * κ + 3) ^ 2 * 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ κ * (2 * (2 * κ + 3) ^ 2 * 2) := mul_le_mul_of_nonneg_right hcanon (by positivity)
    _ = 4 * κ * (2 * κ + 3) ^ 2 := by ring

end Submission.Obl.k4_clean_cover_graph_atlas
