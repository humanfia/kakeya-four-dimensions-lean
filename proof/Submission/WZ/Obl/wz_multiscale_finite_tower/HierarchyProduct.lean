-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyProduct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyAnalysis
import Submission.WZ.Obl.wz_multiscale_finite_tower.Cardinality

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya

lemma HierarchyControl.mono_error {d θ θ' g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') :
    HierarchyControl d θ' g gap T := by
  have hc : d ^ (-θ) ≤ d ^ (-θ') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  refine { H with
    count := fun j hj k => WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexCount_mono hc (H.count j hj k)
    slab := fun j hj k => WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_mono hc (H.slab j hj k)
    balanced := ?_ }
  intro j hj i hi k hk
  exact (H.balanced j hj i hi k hk).trans
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))

lemma volumeFactor_card_loss {s N M R σ ω : ℝ} (hs : 0 < s) (hN : 0 < N)
    (hM : 0 < M) (hR : 1 ≤ R) (hNM : N ≤ R * M) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    volumeFactor σ ω s N ≤ R * volumeFactor σ ω s M := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hh := volumeFactor_mono_card (ω := ω) hs hN hNM hσ1
  rw [volumeFactor_eq hs (mul_pos hRp hM), Real.mul_rpow hRp.le hM.le] at hh
  have hp : R ^ (1 - σ) ≤ R := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (show 1 - σ ≤ 1 by linarith)
  exact hh.trans (by
    rw [volumeFactor_eq hs hM]
    calc
      _ ≤ R * M ^ (1 - σ) * s ^ (ω + 2 - σ) := by gcongr
      _ = _ := by ring)

lemma product_reverse_ratios (f : ℕ → ℝ) (J : ℕ)
    (hf : ∀ j, j ≤ J → f j ≠ 0) :
    (∏ j ∈ Finset.range J, f j / f (j + 1)) = f 0 / f J := by
  induction J with
  | zero => simp [hf 0 le_rfl]
  | succ J ih =>
    rw [Finset.prod_range_succ, ih (fun j hj => hf j (by omega))]
    field_simp [hf J (by omega), hf (J + 1) le_rfl]

lemma HierarchyAnalysis.edge_ratio {d θ g gap ρ σ ω K : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {E : Set Space} (A : HierarchyAnalysis T E d θ ρ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) {j : ℕ} (hj : j < J)
    {k : Fin (T.layer j).card} {m : ℕ} (hm : 0 < m)
    (e : Fin m → Fin (T.layer (j + 1)).card) (hep : ∀ i, T.parent j (e i) = k)
    (hcard : m = {i | T.parent j i = k}.ncard)
    (hV : ENNReal.ofReal (K * (T.layer j).radius ^ 2 *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m) ≤
        volume (⋃ i, A.shading (j + 1) (e i))) :
    (ρ / 256) * d ^ (2 * θ) * K *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius)
        ((T.layer (j + 1)).card / (T.layer j).card) ≤ A.density j / A.density (j + 1) := by
  have hr := H.positive j hj.le
  have hs := H.positive (j + 1) (by omega)
  have ht := A.positive j hj.le
  have ht' := A.positive (j + 1) (by omega)
  have hRp : 0 < (d ^ (-θ)) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hd _)
  have hR : 1 ≤ (d ^ (-θ)) ^ 2 := by
    have hh : 1 ≤ d ^ (-θ) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr hθ)
    nlinarith
  have hN : 0 < ((T.layer (j + 1)).card : ℝ) / (T.layer j).card :=
    div_pos (Nat.cast_pos.mpr (T.layer (j + 1)).card_pos)
    (Nat.cast_pos.mpr (T.layer j).card_pos)
  have havg : ((T.layer (j + 1)).card : ℝ) / (T.layer j).card ≤ (d ^ (-θ)) ^ 2 * m := by
    rw [hcard]
    exact TubeHierarchy.branch_average_lower H hd.le hj k
  have hvf := volumeFactor_card_loss (ω := ω) (div_pos hs hr) hN (Nat.cast_pos.mpr hm) hR havg hσ hσ1
  have hb := (mul_le_mul' le_rfl hV).trans (A.transfer j hj k m e hep)
  rw [← ENNReal.ofReal_mul (mul_nonneg hρ ht'.le)] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg (by norm_num) ht.le) (sq_nonneg _))).mp hb
  have hlocal : ρ * A.density (j + 1) * K *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m ≤ 256 * A.density j := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
    nlinarith only [hb']
  have hglobal : ρ * A.density (j + 1) * K *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius)
        ((T.layer (j + 1)).card / (T.layer j).card) ≤
      (d ^ (-θ)) ^ 2 * (256 * A.density j) := by
    calc
      _ ≤ ρ * A.density (j + 1) * K * ((d ^ (-θ)) ^ 2 *
          volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m) :=
        mul_le_mul_of_nonneg_left hvf (by positivity)
      _ = (d ^ (-θ)) ^ 2 * (ρ * A.density (j + 1) * K *
          volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal hRp.le
  have he : d ^ (2 * θ) * (d ^ (-θ)) ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hd.le, ← Real.rpow_add hd]
    ring_nf
    exact Real.rpow_zero d
  apply (le_div_iff₀ ht').mpr
  have hh := mul_le_mul_of_nonneg_left hglobal (Real.rpow_nonneg hd.le (2 * θ))
  rw [← mul_assoc (d ^ (2 * θ)) ((d ^ (-θ)) ^ 2) (256 * A.density j), he, one_mul] at hh
  nlinarith only [hh]

def FibreVolumeBound {J : ℕ} {T : TubeHierarchy J} {E : Set Space} {d θ ρ : ℝ}
    (A : HierarchyAnalysis T E d θ ρ) (σ ω : ℝ) (j : ℕ) (K : ℝ) : Prop :=
  ∃ k : Fin (T.layer j).card, ∃ m : ℕ, ∃ e : Fin m → Fin (T.layer (j + 1)).card,
    0 < m ∧ (∀ i, T.parent j (e i) = k) ∧ m = {i | T.parent j i = k}.ncard ∧
    ENNReal.ofReal (K * (T.layer j).radius ^ 2 *
      volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius) m) ≤
        volume (⋃ i, A.shading (j + 1) (e i))

/-- Multiplying local density ratios produces the global volume factor, with all
losses explicit and no changes to the reference union. -/
theorem HierarchyAnalysis.volume_product {d θ g gap ρ σ ω : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) {E : Set Space} (A : HierarchyAnalysis T E d θ ρ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (K : ℕ → ℝ) (hK : ∀ j, j < J → 0 ≤ K j)
    (hlocal : ∀ j, j < J → FibreVolumeBound A σ ω j (K j)) :
    ENNReal.ofReal (d ^ θ * ((ρ / 256) * d ^ (2 * θ)) ^ J *
      (∏ j ∈ Finset.range J, K j) * volumeFactor σ ω d (T.layer J).card) ≤ volume E := by
  classical
  let V : ℕ → ℝ := fun j => volumeFactor σ ω ((T.layer (j + 1)).radius / (T.layer j).radius)
    ((T.layer (j + 1)).card / (T.layer j).card)
  have hV (j) (hj : j < J) : 0 ≤ V j := by
    have hr := H.positive j hj.le
    have hs := H.positive (j + 1) (by omega)
    dsimp [V, volumeFactor]
    positivity
  have he (j) (hj : j < J) : (ρ / 256) * d ^ (2 * θ) * K j * V j ≤
      A.density j / A.density (j + 1) := by
    obtain ⟨k, m, e, hm, hep, hc, hv⟩ := hlocal j hj
    exact A.edge_ratio H hd hd1 hθ hρ (hK j hj) hσ hσ1 hj hm e hep hc hv
  have hp := Finset.prod_le_prod₀
    (fun j hj => show 0 ≤ (ρ / 256) * d ^ (2 * θ) * K j * V j by
      have hk := hK j (Finset.mem_range.mp hj)
      have hv := hV j (Finset.mem_range.mp hj)
      positivity)
    (fun j hj => he j (Finset.mem_range.mp hj))
  rw [product_reverse_ratios A.density J (fun j hj => (A.positive j hj).ne'), A.terminal, div_one] at hp
  have hprodV : (∏ j ∈ Finset.range J, V j) = volumeFactor σ ω d (T.layer J).card := by
    exact product_tower_factors σ ω d (T.layer J).card J
      (fun j => (T.layer j).radius) (fun j => (T.layer j).card) H.positive
      (fun j _ => Nat.cast_pos.mpr (T.layer j).card_pos) H.root_radius
      (by rw [H.root_card]; norm_num) H.bottom_radius rfl
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, hprodV] at hp
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) A.root
  have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hd.le θ)
  simpa only [mul_assoc] using hh

lemma HierarchyAnalysis.endpoint_fibre {σ ω d θ g gap ρ a loss θE d₀ : ℝ}
    {J : ℕ} {T : TubeHierarchy J} (H : HierarchyControl d θ g gap T)
    {E : Set Space} (A : HierarchyAnalysis T E d θ ρ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdd : d ≤ d₀) (hθ : θ ≤ θE)
    (HE : ∀ d r s : ℝ, 0 < d → d ≤ 1 → d ≤ d₀ → 0 < r → r ≤ 1 →
      0 < s → d * r ≤ s → s ≤ r → ∀ y w : Space, ‖w‖ = 1 → ∀ n x v Y,
      PhysicalFrame d r s θE y w n x v Y →
      ENNReal.ofReal (a * d ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n) ≤ volume (⋃ i, Y i))
    {j : ℕ} (hj : j < J) : FibreVolumeBound A σ ω j (a * d ^ loss) := by
  let k : Fin (T.layer j).card := ⟨0, (T.layer j).card_pos⟩
  obtain ⟨m, e, hm, he, hrange, hF⟩ := H.physical_fibre hd hj (A.shading (j + 1))
    (A.measurable (j + 1) (by omega)) (A.containment (j + 1) (by omega))
    (A.mass (j + 1) (by omega)) k
  have hep (i : Fin m) : T.parent j (e i) = k := by
    have hi : e i ∈ Set.range e := ⟨i, rfl⟩
    simpa only [hrange, Set.mem_setOf_eq] using hi
  refine ⟨k, m, e, hF.1, hep, hm, ?_⟩
  exact HE d (T.layer j).radius (T.layer (j + 1)).radius hd hd1 hdd
    (H.positive j hj.le) (H.radius_bounds hj.le).2 (H.positive (j + 1) (by omega))
    ((le_div_iff₀ (H.positive j hj.le)).mp (H.ratio_bounds hd.le hj).1)
    (H.decreasing j hj).le _ _ ((T.layer j).unit k) m _ _ _ (hF.mono hd hd1 hθ)

end WangZahlLot.Obl.wz_multiscale_finite_tower
