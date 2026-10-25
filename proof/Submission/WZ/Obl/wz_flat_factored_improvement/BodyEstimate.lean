-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyBalance
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCounts
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyScalar
import Submission.WZ.Obl.wz_flat_factored_improvement.DensityEstimate

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (AffineCell)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst netConst_pos asm_netConst_le_one)

/-- The body form of the tube estimate. The global packing coefficient is sufficient
for both applications in the flat factorization argument. -/
def BodyEstimate (σ u : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A η δ₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
      (x : Fin n → Space) (B w m l P : ℝ),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 1 ≤ l → 1 ≤ P →
    BodyGeometry U x δ B w → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
    (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
    BodyConvexCount U w m → BodySlabCount U l → BodyPacking U w P →
    ENNReal.ofReal (A * δ ^ ε * B ^ u * bodyWeight σ w m l P n) ≤ volume (⋃ i, Y i)

set_option maxHeartbeats 1000000 in
theorem body_estimate_of_tube_estimate {σ u : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hu : 0 < u) (hE : TubeEstimate σ u) : BodyEstimate σ u := by
  intro ε hε
  obtain ⟨A, p, hA, hp, HE⟩ := tube_estimate_with_density hσ hσhalf hu.le hE
    (by positivity : 0 < ε / 2)
  obtain ⟨c₀, hc₀, hcover⟩ := cover_body_cell
  let c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ zero_lt_one
  have hc1 : c ≤ 1 := min_le_right _ _
  let Z := u + ε / 2 + 9 * p + 2 * σ + 2
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let s := ε / (4 * Z)
  have hs : 0 < s := div_pos hε (mul_pos (by norm_num) hZ)
  have hsZ : s * Z = ε / 4 := by dsimp [s]; field_simp
  obtain ⟨η, hη, δ₀, hδ₀, hδ₀small, Hcells⟩ := body_cells s hs
  obtain ⟨b, hb⟩ := exists_nat_gt (100 / s)
  have hbpos : 0 < b := by
    have : (0 : ℝ) < b := lt_trans (by positivity) hb
    exact_mod_cast this
  have hb' : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hbpos
  have hsb : 100 < s * b := by
    have h := (div_lt_iff₀ hs).mp hb
    nlinarith
  let t := netConst / (b : ℝ)
  have ht : 0 < t := div_pos netConst_pos hb'
  have ht1 : t ≤ 1 := by
    rw [div_le_one hb']
    exact asm_netConst_le_one.trans hb1
  let A' := A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (49152 : ℝ) ^ (-σ) * c ^ p * t ^ (1 + σ)
  have hA' : 0 < A' := by dsimp [A']; positivity
  refine ⟨A', η, δ₀, hA', hη, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδmax n U Y x B w m l P hn hnmax hδB hw hm hl hP F hYm hYU hYd hconv hslab hpack
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : 0 < m := zero_lt_one.trans_le hm
  have hl' : 0 < l := zero_lt_one.trans_le hl
  have hP' : 0 < P := zero_lt_one.trans_le hP
  have hB : 0 < B := hδ.trans_le hδB
  have hδsmall := hδmax.trans hδ₀small
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδlt : δ < 1 := hδsmall.trans_lt (by norm_num)
  let h := δ ^ s
  have hh : 0 < h := Real.rpow_pos_of_pos hδ _
  have hh1 : h ≤ 1 := Real.rpow_le_one hδ.le hδ1 hs.le
  let R := δ ^ (-s)
  have hR : 1 < R := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδlt (neg_neg_of_pos hs)
  have hnR : (n : ℝ) < R ^ b := by
    apply hnmax.trans_lt
    dsimp [R]
    rw [← Real.rpow_mul_natCast hδ.le]
    exact Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by nlinarith)
  let τ := netConst / ((b : ℝ) * R)
  have hτ : 0 < τ := div_pos netConst_pos (mul_pos hb' (by linarith : 0 < R))
  have hτeq : τ = t * h := by
    dsimp [τ, t, R, h]
    rw [Real.rpow_neg hδ.le]
    field_simp
  have hτ1 : τ ≤ 1 := by rw [hτeq]; exact (mul_le_mul ht1 hh1 hh.le (by norm_num)).trans_eq (by ring)
  let d := c * h ^ (9 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    exact (mul_le_mul hc1 (pow_le_one₀ hh.le hh1) (by positivity) (by norm_num)).trans_eq (by ring)
  obtain ⟨K, L, hKh, H, hdisj, hmass⟩ := Hcells δ hδ hδmax n U Y x B w hn hnmax hB.le hw F hYm hYU hYd
  let G : Fin L.length → AffineCell n K := L.get
  have hG (j : Fin L.length) : BodyCellValid U Y B h (G j) := (H _ (List.get_mem L j)).1
  have hV (j : Fin L.length) : Nonempty (BalancedBodyCover (G j) (c₀ * h ^ 9) τ) := by
    obtain ⟨V⟩ := hcover n K U Y B h (G j) hh hKh (hG j)
    exact balance_body_cover V hbpos hR hnR
  let V (j : Fin L.length) := Classical.choice (hV j)
  let C := bodyCellFactor σ u (ε / 2) A p B h τ d m l n P w
  have hC : 0 < C := bodyCellFactor_pos hA hB hh hτ hd hm' hl' hn' hP' hw
  have hlocal (j : Fin L.length) :
      ENNReal.ofReal (C * ((G j).indices.card : ℝ)) ≤
        ENNReal.ofReal (G j).jacobian * volume (⋃ a, (V j).shading a) := by
    let ρ := 4 * (G j).b
    let D := (G j).jacobian
    let q : ℝ := (V j).multiplicity
    let N : ℝ := (V j).count
    have hρ : 0 < ρ := by dsimp [ρ, AffineCell.b]; positivity
    have hρsmall : ρ ≤ 1 / 100 := by dsimp [ρ]; linarith [(hG j).small]
    have hρ1 : ρ ≤ 1 := hρsmall.trans (by norm_num)
    have hD : 0 < D := (hG j).jacobian_pos
    have hq : 0 < q := by dsimp [q]; exact_mod_cast (V j).multiplicity_pos
    have hN : 0 < N := by dsimp [N]; exact_mod_cast (V j).count_pos
    have whole : ∀ a, ∀ i ∈ (V j).fiber a,
        U i ⊆ (G j).affine '' Tube ρ ((V j).start a) ((V j).direction a) :=
      fun a i hi => ((hG j).whole i ((V j).fiber_indices a hi)).trans
        (image_mono ((V j).whole a i hi))
    have hcbase := body_convex_transfer hw hm'.le hD hρ (V j).multiplicity_pos
      (G j).affine (V j).start (V j).direction (V j).fiber (V j).fiber_card
      (V j).fiber_disjoint whole (hG j).volume_identity hconv
    let M := 384 * m * D * ρ ^ 2 / (q * w)
    have hM : 1 ≤ M := by
      have hnorm := WangZahlLot.Obl.wz_affine_packet_counting_transfer.constant_lower hρ hρ1
        (by positivity : 0 ≤ m * D * ρ ^ 2 / (q * w)) (V j).count_pos
        (V j).start (V j).direction (V j).unit_direction hcbase
      convert hnorm using 1 <;> dsimp [M] <;> ring
    have hcM : ConvexCount ρ M (V j).count (V j).start (V j).direction := by
      apply WangZahlLot.Obl.wz_affine_packet_counting_transfer.convex_count_mono
        (m := m * D * ρ ^ 2 / (q * w)) ?_ hcbase
      dsimp [M]
      apply div_le_div_of_nonneg_right _ (mul_pos hq hw).le
      nlinarith [mul_nonneg (mul_pos hm' hD).le (sq_nonneg ρ)]
    have hL : 1 ≤ (h * τ)⁻¹ := by
      rw [one_le_inv₀ (mul_pos hh hτ)]
      exact mul_le_one₀ hh1 hτ.le hτ1
    have hdense : ∀ a, ENNReal.ofReal (d * ρ ^ 2) ≤ volume ((V j).shading a) := by
      intro a
      apply (ENNReal.ofReal_le_ofReal _).trans ((V j).density a)
      dsimp [d, ρ]
      gcongr
      exact min_le_left _ _
    have HEj := HE ρ d M (h * τ)⁻¹ hρ hρsmall hd hd1 hM hL (V j).count
      (V j).start (V j).direction (V j).shading (V j).count_pos (V j).unit_direction
      (V j).bounded (V j).separated (V j).measurable (V j).shading_tube hdense hcM
      (balanced_body_slabs (hG j) (V j) hh hτ)
    have hsl := body_slab_transfer hl'.le hD (V j).count_pos (V j).multiplicity_pos
      (G j).affine (V j).start (V j).direction (V j).fiber (V j).fiber_card
      (V j).fiber_disjoint whole (V j).bounded F.diameter (hG j).volume_identity hslab
    let a₀ : Fin (V j).count := ⟨0, (V j).count_pos⟩
    have hpk := body_packing_fiber hw hP'.le hD hρ hρ1 (G j).affine
      ((V j).start a₀) ((V j).direction a₀) ((V j).unit_direction a₀)
      ((V j).fiber a₀) ((V j).fiber_card a₀) (whole a₀) (hG j).volume_identity hpack
    have hscale : B * h ≤ ρ := by
      have Hwidth := (hG j).width
      dsimp [ρ]
      nlinarith [mul_pos hB hh]
    have hnum := body_packet_scalar (p := p) hσ (by positivity : 0 ≤ u + ε / 2)
      hA hd hρ hm' hD hq hw hh hτ hN hB hl' hn' hP'
      (Nat.cast_nonneg (G j).indices.card) hscale (V j).retained hsl hpk
    apply (ENNReal.ofReal_le_ofReal hnum).trans
    rw [ENNReal.ofReal_mul hD.le]
    exact mul_le_mul' le_rfl HEj
  have hmass' : h * (n : ℝ) ≤ ∑ j, ((G j).indices.card : ℝ) := by
    have he := congrArg List.sum (List.map_ofFn (f := L.get)
      (g := fun G : AffineCell n K => (G.indices.card : ℝ)))
    have he' : (∑ j, ((G j).indices.card : ℝ)) = (L.map fun G => (G.indices.card : ℝ)).sum := by
      simpa only [List.ofFn_get, List.sum_ofFn, Function.comp_apply, G] using he.symm
    rwa [he']
  have hsum : ENNReal.ofReal (C * (h * n)) ≤ volume (⋃ i, Y i) := by
    calc
      _ ≤ ENNReal.ofReal (C * ∑ j, ((G j).indices.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmass' hC.le)
      _ = ∑ j, ENNReal.ofReal (C * ((G j).indices.card : ℝ)) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        intro j _
        positivity
      _ ≤ ∑ j, ENNReal.ofReal (G j).jacobian * volume (⋃ a, (V j).shading a) :=
        Finset.sum_le_sum (fun j _ => hlocal j)
      _ ≤ _ := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.asm_transport
        (fun j => (G j).indices) (fun j => (G j).affine) (fun j => (G j).jacobian)
        (fun j => (G j).shading) Y (fun j => (V j).shading)
        (fun j => (hG j).volume_identity) (fun j => (V j).measurable)
        (fun j => (V j).shading_cell)
        (fun j i hi => ((hG j).shading i hi).trans inter_subset_right) (by
          intro j k hjk
          rcases lt_or_gt_of_ne hjk with hjk | hkj
          · exact List.pairwise_iff_get.mp hdisj _ _ hjk
          · exact (List.pairwise_iff_get.mp hdisj _ _ hkj).symm)
  have hfactor : C * (h * n) = A' * B ^ (u + ε / 2) * δ ^ (s * Z) * bodyWeight σ w m l P n := by
    dsimp [C]
    rw [hτeq]
    exact body_sum_factorization hA hB hδ hc ht hm' hl' hn' hP' hw
  rw [hfactor] at hsum
  apply (ENNReal.ofReal_le_ofReal _).trans hsum
  have hweight : 0 ≤ bodyWeight σ w m l P n := by unfold bodyWeight; positivity
  have hexp : ε / 2 + s * Z ≤ ε := by rw [hsZ]; linarith
  calc
    A' * δ ^ ε * B ^ u * bodyWeight σ w m l P n ≤
        A' * δ ^ (ε / 2 + s * Z) * B ^ u * bodyWeight σ w m l P n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp) hA'.le)
          (Real.rpow_nonneg hB.le u)) hweight
    _ = A' * (δ ^ (ε / 2) * B ^ u) * δ ^ (s * Z) * bodyWeight σ w m l P n := by
      rw [Real.rpow_add hδ]
      ring
    _ ≤ A' * (B ^ (ε / 2) * B ^ u) * δ ^ (s * Z) * bodyWeight σ w m l P n := by
      gcongr
    _ = _ := by rw [← Real.rpow_add hB]; congr 3; ring

end WangZahlLot.Obl.wz_flat_factored_improvement
