-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_filling_volume_gain.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_filling_volume_gain.Geometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Nondegenerate
import Submission.WZ.Obl.wz_flat_factored_improvement.PacketNumerics

/-!
# WZ Lemma 5.17 from the body estimate

The filled boxes, cut to the unit ball, form a family of convex bodies. Each body
contains its own tube, so the convex and slab counts of the tube family bound those
of the bodies, and o065's body estimate (a consequence of `E(σ,ω)`) gives the volume
gain `(b/δ)^ω`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_slab_filling_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyGeometry BodyConvexCount BodySlabCount bodyWeight TubeEstimate
    body_estimate_of_tube_estimate)

abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible
abbrev ConvexCount := WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount
abbrev SlabCount := WangZahlLot.Obl.wz_tower_balanced_refinement.SlabCount

/-- The slab-filling hypothesis `Sf δ b e` of the frozen statement. -/
def SlabFilled (δ b e : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∃ G : Finset (Fin n), δ ^ e * n ≤ (G.card : ℝ) ∧
    ∀ i ∈ G, ∃ (z : Space) (g : Space ≃ₗᵢ[ℝ] Space),
      Tube δ (x i) (v i) ⊆ Box (10 * δ) b 2 z g ∧
      ENNReal.ofReal (δ ^ e) * volume (Box (10 * δ) b 2 z g) ≤
        volume (Box (10 * δ) b 2 z g ∩ ⋃ j, Y j)

/-- Bodies with injectively chosen tubes inside them inherit the convex count. -/
lemma body_convex_count {δ η w : ℝ} (hδ : 0 < δ) (hw : 0 ≤ w) {n N : ℕ}
    {x v : Fin n → Space} (hK : ConvexCount δ (δ ^ (-η)) n x v)
    (φ : Fin N → Fin n) (hφ : Function.Injective φ) {U : Fin N → Set Space}
    (hTU : ∀ j, Tube δ (x (φ j)) (v (φ j)) ⊆ U j) :
    BodyConvexCount U w (w / δ ^ 2 * δ ^ (-η)) := by
  intro Q hQ
  have hc : (Set.ncard {j | U j ⊆ Q} : ℝ) ≤ (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn φ (fun j hj => (hTU j).trans hj) hφ.injOn
  have hk := hK Q hQ
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc ENNReal.ofReal ((Set.ncard {j | U j ⊆ Q} : ℝ) * w)
      ≤ ENNReal.ofReal (w / δ ^ 2 *
          ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show w / δ ^ 2 * ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2) =
          (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) * w by field_simp]
        exact mul_le_mul_of_nonneg_right hc hw
    _ = ENNReal.ofReal (w / δ ^ 2) *
          ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (w / δ ^ 2) * (ENNReal.ofReal (δ ^ (-η)) * volume Q) :=
        mul_le_mul' le_rfl hk
    _ = ENNReal.ofReal (w / δ ^ 2 * δ ^ (-η)) * volume Q := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- Bodies with injectively chosen tubes inside them inherit the slab count. -/
lemma body_slab_count {δ η : ℝ} (hδ : 0 < δ) {n N : ℕ} (hN : 0 < N) {x v : Fin n → Space}
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hF : SlabCount δ (δ ^ (-η)) n x v)
    (φ : Fin N → Fin n) (hφ : Function.Injective φ) {U : Fin N → Set Space}
    (hTU : ∀ j, Tube δ (x (φ j)) (v (φ j)) ⊆ U j) :
    BodySlabCount U (8 * δ ^ (-η) * n / N) := by
  intro ν s r hν hr
  have hc : (Set.ncard {j | U j ⊆ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) ≤
      (Set.ncard {i | Tube δ (x i) (v i) ⊆
        ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn φ
      (fun j hj => subset_inter (hball (φ j)) ((hTU j).trans hj)) hφ.injOn
  have hk := hF ν s r hν hr
  have hvol := WangZahlLot.Obl.wz_grains_nonsingular_slices.nd_slab_volume_le hν s r hr.le
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc ENNReal.ofReal (Set.ncard {j | U j ⊆ {p | |inner ℝ ν p - s| ≤ r}} : ℝ)
      ≤ ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) :=
        ENNReal.ofReal_le_ofReal hc
    _ ≤ ENNReal.ofReal (δ ^ (-η) * n) *
          volume (ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}) := hk
    _ ≤ ENNReal.ofReal (δ ^ (-η) * n) * ENNReal.ofReal (8 * r) := mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal (8 * δ ^ (-η) * n / N * N * r) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- The body weight with the inherited coefficients; the volume scale `w` cancels. -/
lemma bodyWeight_eq {σ δ η w n N : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hn : 0 < n) (hN : 0 < N) :
    bodyWeight σ w (w / δ ^ 2 * δ ^ (-η)) (8 * δ ^ (-η) * n / N) (w / δ ^ 2 * δ ^ (-η)) N =
      (8 : ℝ) ^ (-σ) * δ ^ (η * (1 + σ / 2)) * δ ^ (2 - σ) * n ^ (-σ) * N := by
  unfold bodyWeight
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  push_cast
  ring

/-- The final numerical comparison, in logarithms. -/
lemma final_comparison {σ ω α εB η e c κ A δ B b n N : ℝ} (hω : 0 ≤ ω)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hn : 0 < n) (hN : 0 < N)
    (hκ : κ = A * (8 : ℝ) ^ (-σ) * (50 : ℝ) ^ (-ω)) (hBb : b / 50 ≤ B)
    (hb1 : δ ^ (1 - c) ≤ b) (hNn : δ ^ e * n ≤ N)
    (hcoef : 0 ≤ c * ω - α - εB - η * (1 + σ / 2) - e) :
    κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ) ≤
      A * δ ^ εB * B ^ ω *
        ((8 : ℝ) ^ (-σ) * δ ^ (η * (1 + σ / 2)) * δ ^ (2 - σ) * n ^ (-σ) * N) := by
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hLδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hLB : Real.log b - Real.log 50 ≤ Real.log B := by
    rw [← Real.log_div hb.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) hBb
  have hLb : (1 - c) * Real.log δ ≤ Real.log b := by
    rw [← Real.log_rpow hδ]
    exact Real.log_le_log (by positivity) hb1
  have hLN : e * Real.log δ + Real.log n ≤ Real.log N := by
    rw [← Real.log_rpow hδ, ← Real.log_mul (by positivity) hn.ne']
    exact Real.log_le_log (by positivity) hNn
  have hprod : (c * ω - α - εB - η * (1 + σ / 2) - e) * Real.log δ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hLδ
  have hωLB : ω * (Real.log b - Real.log 50) ≤ ω * Real.log B :=
    mul_le_mul_of_nonneg_left hLB hω
  have hωLb : ω * ((1 - c) * Real.log δ) ≤ ω * Real.log b :=
    mul_le_mul_of_nonneg_left hLb hω
  have hlogκ : Real.log κ = Real.log A + (-σ) * Real.log 8 + (-ω) * Real.log 50 := by
    rw [hκ]
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow]
  rw [hlogκ]
  push_cast
  linarith [hLN, hprod, hωLB, hωLb]

set_option maxHeartbeats 1000000 in
/-- The internal form of WZ Lemma 5.17. -/
theorem main {σ ω : ℝ} (hσ : 0 < σ) (hσh : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : TubeEstimate σ ω) {c : ℝ} (hc : 0 < c) :
    ∃ α : ℝ, 0 < α ∧ ∃ e : ℝ, 0 < e ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
      ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ∀ b : ℝ, δ ^ (1 - c) ≤ b → b ≤ 1 → SlabFilled δ b e n x v Y →
      ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) := by
  set α : ℝ := c * ω / 2 with hαdef
  have hα : 0 < α := by positivity
  set εB : ℝ := α / 6 with hεBdef
  have hεB : 0 < εB := by positivity
  obtain ⟨A, ηB, δB, hA, hηB, hδB, hδB100, H⟩ :=
    body_estimate_of_tube_estimate hσ.le hσh hω hE εB hεB
  obtain ⟨dn, hdn, hdn100, Hn⟩ := WangZahlLot.Obl.wz_flat_factored_improvement.tube_number_power_bound
  set e : ℝ := min ηB (α / 6) with hedef
  have he : 0 < e := lt_min hηB (by positivity)
  set η₀ : ℝ := α / 6 with hη₀def
  set κ : ℝ := A * (8 : ℝ) ^ (-σ) * (50 : ℝ) ^ (-ω) with hκdef
  have hκ : 0 < κ := by positivity
  set dc : ℝ := (1 / 16 : ℝ) ^ (1 / c) with hdcdef
  have hdc : 0 < dc := by positivity
  set d₀ : ℝ := min (min δB dn) (min (1 / 1000) dc) with hd₀def
  have hd₀ : 0 < d₀ := lt_min (lt_min hδB hdn) (lt_min (by norm_num) hdc)
  refine ⟨α, hα, e, he, κ, hκ, η₀, by positivity, d₀, hd₀,
    (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num)), ?_⟩
  intro δ hδ hδd η hη hηη n x v Y hAdm b hb1 hb2 hSf
  -- scales
  have hδδB : δ ≤ δB := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδdn : δ ≤ dn := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1000 : δ ≤ 1 / 1000 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδdc : δ ≤ dc := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδ1000.trans (by norm_num)
  have hδlt1 : δ < 1 := hδ1000.trans_lt (by norm_num)
  have hδc : δ ^ c ≤ 1 / 16 := by
    calc δ ^ c ≤ dc ^ c := Real.rpow_le_rpow hδ.le hδdc hc.le
      _ = 1 / 16 := by
        rw [hdcdef, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hc.ne', Real.rpow_one]
  have hb16 : 16 * δ ≤ b := by
    have hsplit : δ ^ (1 - c) = δ * (δ ^ c)⁻¹ := by
      rw [Real.rpow_sub hδ, Real.rpow_one, div_eq_mul_inv]
    have hinv : 16 ≤ (δ ^ c)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      linarith
    nlinarith [hsplit ▸ hb1]
  have hb0 : 0 < b := by linarith
  -- the admissible family
  obtain ⟨hn, htube, hX, hdens, hK, hF⟩ := hAdm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the filled boxes
  obtain ⟨G, hGcard, hbox⟩ := hSf
  set N : ℕ := G.card with hNdef
  have hNn : N ≤ n := by
    have := Finset.card_le_univ G
    simpa using this
  have hNpos : 0 < N := by
    have h1 : (0 : ℝ) < δ ^ e * n := by positivity
    have h2 : (0 : ℝ) < N := h1.trans_le hGcard
    exact_mod_cast h2
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  let φ : Fin N ↪o Fin n := G.orderEmbOfFin hNdef.symm
  have hφmem : ∀ j, φ j ∈ G := fun j => G.orderEmbOfFin_mem hNdef.symm j
  choose z g hzg using fun j : Fin N => hbox (φ j) (hφmem j)
  set U : Fin N → Set Space := fun j => Box (10 * δ) b 2 (z j) (g j) ∩ closedBall 0 1
    with hUdef
  set Y' : Fin N → Set Space := fun j => Box (10 * δ) b 2 (z j) (g j) ∩ ⋃ k, Y k
    with hY'def
  set xc : Fin N → Space := fun j => x (φ j) + (1 / 2 : ℝ) • v (φ j) with hxcdef
  set B : ℝ := min (b / 2) (1 / 25) / 2 with hBdef
  set w : ℝ := δ * b / 16 with hwdef
  have hw : 0 < w := by positivity
  set mB : ℝ := w / δ ^ 2 * δ ^ (-η) with hmBdef
  set lB : ℝ := 8 * δ ^ (-η) * n / N with hlBdef
  have hfacts := fun j => filled_body_facts hδ hδ1000 (by linarith) hb2
    (htube (φ j)).1 (htube (φ j)).2.1 (hzg j).1
  have hgeom : BodyGeometry U xc δ B w :=
    { compact := fun j => (hfacts j).1
      convex := fun j => (hfacts j).2.1
      bounded := fun j => inter_subset_right
      interior := fun j => (hfacts j).2.2.1
      diameter := fun j => (hfacts j).2.2.2.1
      width := fun j => (hfacts j).2.2.2.2.1
      volume_bounds := fun j => ⟨(hfacts j).2.2.2.2.2.1, (hfacts j).2.2.2.2.2.2.1⟩ }
  have hTU : ∀ j, Tube δ (x (φ j)) (v (φ j)) ⊆ U j := fun j => (hfacts j).2.2.2.2.2.2.2
  have hδpow1 : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hmB : 1 ≤ mB := by
    have h1 : 1 ≤ w / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity), hwdef]
      have h16 : δ ≤ b / 16 := by linarith
      calc 1 * δ ^ 2 = δ * δ := by ring
        _ ≤ δ * (b / 16) := mul_le_mul_of_nonneg_left h16 hδ.le
        _ = δ * b / 16 := by ring
    rw [hmBdef]
    exact one_le_mul_of_one_le_of_one_le h1 hδpow1
  have hlB : 1 ≤ lB := by
    rw [hlBdef, le_div_iff₀ hN']
    have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have h8 : (n : ℝ) ≤ 8 * δ ^ (-η) * n := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 8 * δ ^ (-η) by linarith) hn'.le
      linarith
    linarith
  have hNbound : (N : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have h1 : (n : ℝ) ≤ δ ^ (-10 : ℝ) :=
      Hn δ hδ hδdn n x v (fun i => (htube i).1) (fun i => (htube i).2.1) hX
    have h2 : δ ^ (-10 : ℝ) ≤ δ ^ (-100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
    have : (N : ℝ) ≤ n := by exact_mod_cast hNn
    linarith
  have hδB' : δ ≤ B := by
    rw [hBdef]
    have : 2 * δ ≤ min (b / 2) (1 / 25) := le_min (by linarith) (by linarith)
    linarith
  have hYm : ∀ j, MeasurableSet (Y' j) := fun j =>
    (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _).measurableSet.inter
      (MeasurableSet.iUnion fun k => (htube k).2.2.1)
  have hUY : (⋃ k, Y k) ⊆ closedBall (0 : Space) 1 := by
    refine iUnion_subset fun k => ?_
    exact (htube k).2.2.2.trans ((htube k).2.1.trans ball_subset_closedBall)
  have hYU : ∀ j, Y' j ⊆ U j := fun j => inter_subset_inter_right _ hUY
  have hden : ∀ j, ENNReal.ofReal (δ ^ ηB) * volume (U j) ≤ volume (Y' j) := by
    intro j
    have hpow : δ ^ ηB ≤ δ ^ e := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
    calc ENNReal.ofReal (δ ^ ηB) * volume (U j)
        ≤ ENNReal.ofReal (δ ^ e) * volume (Box (10 * δ) b 2 (z j) (g j)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) (measure_mono inter_subset_left)
      _ ≤ volume (Y' j) := (hzg j).2
  have hconv : BodyConvexCount U w mB := body_convex_count hδ hw.le hK φ φ.injective hTU
  have hslab : BodySlabCount U lB :=
    body_slab_count hδ hNpos (fun i => (htube i).2.1) hF φ φ.injective hTU
  have hpack := WangZahlLot.Obl.wz_clustered_cover_volume_gain.packing_of_convex_count hw.le hconv
  have hbound := H δ hδ hδδB N U Y' xc B w mB lB mB hNpos hNbound hδB' hw hmB hlB hmB hgeom
    hYm hYU hden hconv hslab hpack
  rw [hmBdef, hlBdef, bodyWeight_eq hδ hw hn' hN'] at hbound
  have hYY : volume (⋃ j, Y' j) ≤ volume (⋃ i, Y i) :=
    measure_mono (iUnion_subset fun j => inter_subset_right)
  refine le_trans ?_ (hbound.trans hYY)
  apply ENNReal.ofReal_le_ofReal
  -- the final comparison
  have hB0 : 0 < B := lt_of_lt_of_le hδ hδB'
  have hBb : b / 50 ≤ B := by
    rw [hBdef]
    have : b / 25 ≤ min (b / 2) (1 / 25) := le_min (by linarith) (by linarith)
    linarith
  have hcoef : 0 ≤ c * ω - α - εB - η * (1 + σ / 2) - e := by
    have h1 : η * (1 + σ / 2) ≤ η₀ * (5 / 4) :=
      mul_le_mul hηη (by linarith) (by positivity) (by positivity)
    have h2 : e ≤ α / 6 := min_le_right _ _
    rw [hη₀def] at h1
    rw [hεBdef]
    have hcω : c * ω = 2 * α := by rw [hαdef]; ring
    rw [hcω]
    linarith
  exact final_comparison hω.le hδ hδ1 hA hB0 hb0 hn' hN' hκdef hBb hb1 hGcard hcoef

end WangZahlLot.Obl.wz_slab_filling_volume_gain
