import Submission.Obl.k4_horizontal_wide_interval_return.Core.Datum
import Submission.Obl.k4_horizontal_wide_interval_return.Core.StripCap
import Submission.Obl.k4_horizontal_wide_interval_return.Core.SheetGeometry
import Submission.Obl.k4_horizontal_wide_interval_return.Core.KeyCompare

/-!
# Interval ceilings, jet counts and closeness for the layers of the datum

These are the three hypotheses of `key_compare`, derived from the frozen joint caps
(`chart_strip_cap`), the layer floors and the layer fits.  All numerical requirements on the
resolutions are explicit hypotheses; they are discharged for large `N` elsewhere.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D
open Submission.Obl.k4_horizontal_wide_interval_return.CompareSheets

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace LayerDatum

variable {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
  (L : LayerDatum cfg k ε R χ D depth)

theorem mem_bins {h : Fin 3} {i : Fin (L.np h)} {l : α} (hl : l ∈ L.C h i) :
    ⌊cfg.b k l 3 / χ⌋ = L.qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = L.qp h i 1 ∧
      ⌊cfg.b k l 1 / D⌋ = L.qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε) :=
  (L.piece h i).1 l hl

theorem key_bound (h : Fin 3) (i : Fin (L.np h)) :
    |(L.qp h i 0 : ℝ) * χ| + |(L.qp h i 1 : ℝ) * χ| + |(L.qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε :=
  (L.piece h i).2.1

theorem degree (h : Fin 3) (i : Fin (L.np h)) : (L.G h i).totalDegree ≤ 2 :=
  (L.piece h i).2.2.1

/-- The strip of a piece in the form `y₀ + t v + D w`. -/
theorem strip (h : Fin 3) (i : Fin (L.np h)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, (L.qp h i 2 : ℝ) * D + t * -((L.qp h i 1 : ℝ) * χ) + D * w]
        (L.G h i)| ≤ cfg.N k ^ ε := by
  intro t ht w hw
  have := (L.piece h i).2.2.2.2.1 t ht w hw
  convert this using 4
  ring

theorem fit {h : Fin 3} {i : Fin (L.np h)} {l : α} (hl : l ∈ L.C h i) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |hidden (cfg.b k) (l, t) - MvPolynomial.eval ![t, basePt (cfg.b k) (l, t) 2] (L.G h i)| ≤
      cfg.N k ^ ε * cfg.N k ^ (-depth h) :=
  ((L.piece h i).2.2.2.2.2.1 l hl t ht).2

theorem floor (h : Fin 3) (i : Fin (L.np h)) :
    ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
      cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) ≤
      cfg.ρ k (L.C h i ×ˢ Set.Icc (0 : ℝ) 1) :=
  (L.piece h i).2.2.2.2.2.2

end LayerDatum

/-- The velocity-bin set equals the half-open palette interval. -/
theorem floorBin_eq_Ico {χ : ℝ} (hχ : 0 < χ) (κ0 : ℤ) :
    {w : ℝ | ⌊w / χ⌋ = κ0} = Set.Ico ((κ0 : ℝ) * χ) (((κ0 : ℝ) + 1) * χ) := by
  ext w
  simp only [mem_setOf_eq, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]

/-- The good incidences: unit time, horizontal relation, bounded hidden value. -/
def goodSet (b : α → Fin 6 → ℝ) (ζ₀ Kb : ℝ) : Set (α × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 4 + b p.1 0| ≤ ζ₀ ∧ |hidden b p| ≤ Kb}

/-- A measure dominated by `μ` charges a set only through its good part. -/
theorem le_good {ρs μ : Measure (α × ℝ)} (hle : ρs ≤ μ) {G : Set (α × ℝ)} (hG : μ Gᶜ = 0)
    (S : Set (α × ℝ)) : ρs S ≤ μ (S ∩ G) := by
  have h0 : ρs (S \ G) = 0 := measure_mono_null (fun p hp => hp.2) (le_antisymm
    ((hle Gᶜ).trans hG.le) bot_le)
  calc ρs S ≤ ρs (S ∩ G) + ρs (S \ G) := measure_le_inter_add_diff _ _ _
    _ = ρs (S ∩ G) := by rw [h0, add_zero]
    _ ≤ μ (S ∩ G) := hle _

/-- Strip coordinates of the incidences of a piece stay in `[1/4, 1]`. -/
theorem LayerDatum.etaFun_mem {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) {h : Fin 3} {i : Fin (L.np h)} {p : α × ℝ}
    (hp : p.1 ∈ L.C h i) (hχ : 0 < χ) (hD : 0 < D) {ζ₀ : ℝ}
    (ht : p.2 ∈ Icc (0 : ℝ) 1) (hh : |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀)
    (hdrift : ζ₀ + χ ≤ D / 4) :
    etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D p.2 (basePt (cfg.b k) p 2) ∈
      Icc (1 / 4 : ℝ) 1 := by
  obtain ⟨-, h0, h1, -⟩ := L.mem_bins hp
  have hb1lo : (L.qp h i 2 : ℝ) * D ≤ cfg.b k p.1 1 := by
    have := Int.floor_le (cfg.b k p.1 1 / D); rw [h1, le_div_iff₀ hD] at this; linarith
  have hb1hi : cfg.b k p.1 1 < ((L.qp h i 2 : ℝ) + 1) * D := by
    have := Int.lt_floor_add_one (cfg.b k p.1 1 / D); rw [h1, div_lt_iff₀ hD] at this
    linarith
  have hb0lo : (L.qp h i 1 : ℝ) * χ ≤ cfg.b k p.1 0 := by
    have := Int.floor_le (cfg.b k p.1 0 / χ); rw [h0, le_div_iff₀ hχ] at this; linarith
  have hb0hi : cfg.b k p.1 0 < ((L.qp h i 1 : ℝ) + 1) * χ := by
    have := Int.lt_floor_add_one (cfg.b k p.1 0 / χ); rw [h0, div_lt_iff₀ hχ] at this
    linarith
  rw [abs_le] at hh
  have hdr : |cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ| ≤ D / 4 := by
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨ht0, ht1⟩ := ht
  have hY : basePt (cfg.b k) p 2 = cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 := rfl
  have heq : etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D p.2
      (basePt (cfg.b k) p 2) = (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) +
        p.2 * (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ) / (4 * D) + 1 / 2 := by
    rw [hY]; unfold etaFun; field_simp; ring
  rw [heq]
  have h4D : 0 < 4 * D := by positivity
  have hA : 0 ≤ (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) :=
    div_nonneg (by linarith) h4D.le
  have hA' : (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) ≤ 1 / 4 := by
    rw [div_le_iff₀ h4D]; nlinarith
  have hB : |p.2 * (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ) / (4 * D)| ≤ 1 / 16 := by
    rw [abs_div, abs_mul, abs_of_nonneg ht0, abs_of_pos h4D, div_le_iff₀ h4D]
    nlinarith [abs_nonneg (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ)]
  rw [abs_le] at hB
  constructor <;> linarith [hB.1, hB.2]

/-- **Interval ceiling of one piece** in its strip coordinate. -/
theorem LayerDatum.interval_ceiling {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ Kb : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ Kb)ᶜ = 0) (hζ₀ : 0 ≤ ζ₀)
    {r s' v' : ℝ}
    (hcap : JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' v')
    (hN : 0 < cfg.N k) (hK : 0 ≤ cfg.K k) (hχv : χ = cfg.N k ^ (-v')) (hD : 0 < D)
    (h : Fin 3) (i : Fin (L.np h)) {w x : ℝ} (hw : 0 < w)
    (hfitw : cfg.N k ^ ε * cfg.N k ^ (-depth h) ≤ cfg.N k ^ (-s'))
    (hδχ : (|(L.qp h i 0 : ℝ) * χ| + |(L.qp h i 1 : ℝ) * χ| + χ + 1) * cfg.N k ^ (-r) ≤ χ / 2)
    (hdr : cfg.N k ^ (-r) ≤ 1 / 2)
    (hθ : 1120 * cfg.N k ^ ε * (cfg.N k ^ (-r) +
      (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D)) ≤ cfg.N k ^ (-s'))
    (hdrift : ζ₀ + χ ≤ D / 4)
    (hsmall : (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) ≤ D) :
    L.ρs ((L.C h i ∩ {l | etaOf ((L.qp h i 2 : ℝ) * D) D (cfg.b k l 1) ∈ Icc (x - w) x}) ×ˢ
        univ) ≤
      ENNReal.ofReal (3000 * cfg.K k * (2 : ℕ) * χ * (2 * D * w + χ / 2 + ζ₀) *
        (cfg.N k ^ (-s')) ^ cfg.d) *
        cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) := by
  have hχ : 0 < χ := by rw [hχv]; exact Real.rpow_pos_of_pos hN _
  set y₀ : ℝ := (L.qp h i 2 : ℝ) * D with hy₀
  set vv : ℝ := -((L.qp h i 1 : ℝ) * χ) with hvv
  set Fs := sheetCoeff (L.G h i) y₀ vv D with hFsdef
  have hFs : ∀ k', |Fs k'| ≤ 160 * cfg.N k ^ ε := sheetCoeff_bound (L.degree h i) (L.strip h i)
  have hNε : 0 < cfg.N k ^ ε := Real.rpow_pos_of_pos hN _
  set S := (L.C h i ∩ {l | etaOf y₀ D (cfg.b k l 1) ∈ Icc (x - w) x}) ×ˢ (univ : Set ℝ)
  set E := S ∩ goodSet (cfg.b k) ζ₀ Kb
  refine (le_good (L.le_rho.trans hρμ) hgood S).trans ?_
  set θ : ℝ := 1120 * cfg.N k ^ ε * (cfg.N k ^ (-r) +
      (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D)) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hmain := chart_strip_cap hb hN hK hcap hχv (L.qp h i 0) (L.qp h i 1)
    (ylo := y₀ + 4 * D * (x - w - 1 / 2)) (yhi := y₀ + 4 * D * (x - 1 / 2)) (ζ₀ := ζ₀)
    (W := 2 * cfg.N k ^ (-s')) (θ := θ) (m := 2) (by norm_num)
    (by nlinarith) hζ₀ (by push_cast; linarith) hθ0 hθ hδχ hdr
    (fun t Y => quad2 Fs t (etaFun y₀ vv D t Y)) E ?_ ?_
  · refine hmain.trans (le_of_eq ?_)
    rw [floorBin_eq_Ico hχ]
    congr 2
    ring
  · -- membership in the strip window
    rintro p ⟨⟨⟨hpC, hpη⟩, -⟩, hpt, hph, -⟩
    obtain ⟨h3, h0, -, -⟩ := L.mem_bins hpC
    have hη : etaOf y₀ D (cfg.b k p.1 1) ∈ Icc (x - w) x := hpη
    unfold etaOf at hη
    obtain ⟨hη1, hη2⟩ := hη
    have h4D : 0 < 4 * D := by positivity
    have hlo : y₀ + 4 * D * (x - w - 1 / 2) ≤ cfg.b k p.1 1 := by
      have : x - w - 1 / 2 ≤ (cfg.b k p.1 1 - y₀) / (4 * D) := by linarith
      rw [le_div_iff₀ h4D] at this; linarith
    have hhi : cfg.b k p.1 1 ≤ y₀ + 4 * D * (x - 1 / 2) := by
      have : (cfg.b k p.1 1 - y₀) / (4 * D) ≤ x - 1 / 2 := by linarith
      rw [div_le_iff₀ h4D] at this; linarith
    have hfit := L.fit hpC hpt
    have hval : quad2 Fs p.2 (etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2)) =
        MvPolynomial.eval ![p.2, basePt (cfg.b k) p 2] (L.G h i) :=
      quad2_sheetCoeff_etaFun (L.degree h i) hD.ne' _ _
    have hp0 : basePt (cfg.b k) p 0 = p.2 := rfl
    rw [hp0, hval]
    have hpp : (p.1, p.2) = p := rfl
    rw [hpp] at hfit
    rw [abs_le] at hfit
    refine ⟨h3, h0, hlo, hhi, hpt, hph, ?_, ?_⟩ <;> linarith
  · -- variation of the offset across a base cell
    rintro p ⟨⟨⟨hpC, -⟩, -⟩, hpt, hph, -⟩ y hy
    have hη := L.etaFun_mem hpC hχ hD hpt hph hdrift
    have hp0 : basePt (cfg.b k) p 0 = p.2 := rfl
    have ht0 := hpt.1; have ht1 := hpt.2
    have hy0 := hy 0; have hy2 := hy 2
    rw [hp0] at hy0 ⊢
    have hdη := etaFun_sub (y₀ := y₀) (v := vv) hD p.2 (basePt (cfg.b k) p 2) (y 0) (y 2)
    have hvv' : |vv| = |(L.qp h i 1 : ℝ) * χ| := by rw [hvv, abs_neg]
    rw [hvv'] at hdη
    have hδr : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN _
    have hdη' : |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) - etaFun y₀ vv D (y 0) (y 2)| ≤
        (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) := by
      refine hdη.trans ?_
      have hy2' : |basePt (cfg.b k) p 2 - y 2| ≤ cfg.N k ^ (-r) := hy2
      have hy0' : |p.2 - y 0| ≤ cfg.N k ^ (-r) := hy0
      have hnum : |basePt (cfg.b k) p 2 - y 2| + |(L.qp h i 1 : ℝ) * χ| * |p.2 - y 0| ≤
          (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) := by
        nlinarith [abs_nonneg ((L.qp h i 1 : ℝ) * χ), abs_nonneg (p.2 - y 0)]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    have hdη1 : (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * D)]; linarith
    have hη2 : |etaFun y₀ vv D (y 0) (y 2)| ≤ 2 := by
      rw [abs_le] at hdη' ⊢
      constructor <;> linarith [hη.1, hη.2, hdη'.1, hdη'.2]
    have hlip := quad2_lipschitz (L := 2) hFs
      (t := p.2) (t' := y 0) (η := etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2))
      (η' := etaFun y₀ vv D (y 0) (y 2))
      (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le] at hy0 ⊢; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith [hη.1, hη.2]) hη2
    refine hlip.trans ?_
    rw [hθdef]
    have : |p.2 - y 0| + |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) - etaFun y₀ vv D (y 0) (y 2)| ≤
        cfg.N k ^ (-r) + (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) := by
      linarith
    calc 160 * cfg.N k ^ ε * (1 + 3 * 2) * (|p.2 - y 0| +
          |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) - etaFun y₀ vv D (y 0) (y 2)|)
        ≤ 160 * cfg.N k ^ ε * (1 + 3 * 2) * (cfg.N k ^ (-r) +
          (1 + |(L.qp h i 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D)) := by gcongr
      _ = _ := by ring

/-- **Floors of a family of pieces of one key** are charged to the incidences of their union. -/
theorem LayerDatum.card_floor_le {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ Kb : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ Kb)ᶜ = 0)
    (h : Fin 3) (κ0 : ℤ) (J : Finset (Fin (L.np h))) (hJ : ∀ i ∈ J, L.qp h i 0 = κ0) :
    (J.card : ENNReal) * (ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
      cfg.π k (Set.Ico ((κ0 : ℝ) * χ) (((κ0 : ℝ) + 1) * χ))) ≤
      cfg.μ k ((⋃ i ∈ J, L.C h i ×ˢ Icc (0 : ℝ) 1) ∩ goodSet (cfg.b k) ζ₀ Kb) := by
  calc (J.card : ENNReal) * (ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d /
        cfg.N k ^ ε) * cfg.π k (Set.Ico ((κ0 : ℝ) * χ) (((κ0 : ℝ) + 1) * χ)))
      = ∑ i ∈ J, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
          cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) := by
        rw [Finset.sum_congr rfl (fun i hi => by rw [hJ i hi]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ J, cfg.ρ k (L.C h i ×ˢ Icc (0 : ℝ) 1) :=
        Finset.sum_le_sum fun i _ => L.floor h i
    _ = cfg.ρ k (⋃ i ∈ J, L.C h i ×ˢ Icc (0 : ℝ) 1) := by
        rw [measure_biUnion_finset]
        · intro i _ i' _ hii'
          exact Set.disjoint_prod.mpr (Or.inl (L.disj h i i' hii'))
        · intro i _
          exact (L.meas h i).prod measurableSet_Icc
    _ ≤ cfg.μ k ((⋃ i ∈ J, L.C h i ×ˢ Icc (0 : ℝ) 1) ∩ goodSet (cfg.b k) ζ₀ Kb) :=
        le_good hρμ hgood _

/-- The normalized sheet of a piece in its key's strip. -/
def keySheet (G : MvPolynomial (Fin 2) ℝ) (κ : Fin 3 → ℤ) (χ D a : ℝ) : Fin 6 → ℝ :=
  a⁻¹ • sheetCoeff G ((κ 2 : ℝ) * D) (-((κ 1 : ℝ) * χ)) D

/-- **Jet count at fine scale.** -/
theorem LayerDatum.jet_count_fine {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ Kb : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ Kb)ᶜ = 0) (hζ₀ : 0 ≤ ζ₀)
    {r s' v' : ℝ}
    (hcap : JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r s' v')
    (hN : 0 < cfg.N k) (hK : 0 ≤ cfg.K k) (hχv : χ = cfg.N k ^ (-v')) (hD : 0 < D)
    (h : Fin 3) (κ : Fin 3 → ℤ) {a B M : ℝ} (ha : 0 < a) (ref : Fin 6 → ℝ)
    (hB : ∀ i, L.qp h i = κ → ∀ k', |keySheet (L.G h i) κ χ D a k'| ≤ B)
    (hβ : 18 * a * M = cfg.N k ^ (-s'))
    (hfitw : cfg.N k ^ ε * cfg.N k ^ (-depth h) ≤ 3 * a * M)
    (hδχ : (|(κ 0 : ℝ) * χ| + |(κ 1 : ℝ) * χ| + χ + 1) * cfg.N k ^ (-r) ≤ χ / 2)
    (hdr : cfg.N k ^ (-r) ≤ 1 / 2)
    (hθ : a * (B + M) * 7 * (cfg.N k ^ (-r) + (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D)) ≤
      18 * a * M)
    (hdrift : ζ₀ + χ ≤ D / 4)
    (hsmall : (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) ≤ D) :
    ((Finset.univ.filter (fun i => L.qp h i = κ ∧
        ∀ k', |keySheet (L.G h i) κ χ D a k' - ref k'| ≤ M)).card : ENNReal) *
      (ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
        cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ))) ≤
      ENNReal.ofReal (3000 * cfg.K k * (1 : ℕ) * χ * (D / 2 + χ / 2 + ζ₀) *
        (18 * a * M) ^ cfg.d) *
        cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ)) := by
  classical
  have hχ : 0 < χ := by rw [hχv]; exact Real.rpow_pos_of_pos hN _
  set J := Finset.univ.filter (fun i => L.qp h i = κ ∧
    ∀ k', |keySheet (L.G h i) κ χ D a k' - ref k'| ≤ M) with hJdef
  refine (L.card_floor_le hρμ hgood h (κ 0) J (fun i hi => by
    rw [(Finset.mem_filter.mp hi).2.1])).trans ?_
  by_cases hJne : J.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJne]
    simp
  obtain ⟨i₀, hi₀⟩ := hJne
  have hi₀' := (Finset.mem_filter.mp hi₀).2
  have href : ∀ k', |ref k'| ≤ B + M := by
    intro k'
    have h1 := hB i₀ hi₀'.1 k'
    have h2 := hi₀'.2 k'
    calc |ref k'| ≤ |keySheet (L.G h i₀) κ χ D a k'| +
          |keySheet (L.G h i₀) κ χ D a k' - ref k'| := by
          have := abs_sub_abs_le_abs_sub (keySheet (L.G h i₀) κ χ D a k') (ref k')
          have := abs_sub_abs_le_abs_sub (ref k') (keySheet (L.G h i₀) κ χ D a k')
          rw [abs_sub_comm] at this
          linarith [abs_nonneg (keySheet (L.G h i₀) κ χ D a k' - ref k')]
      _ ≤ B + M := add_le_add h1 h2
  have hBM : 0 ≤ B + M := (abs_nonneg _).trans (href 0)
  set y₀ : ℝ := (κ 2 : ℝ) * D
  set vv : ℝ := -((κ 1 : ℝ) * χ)
  set θ : ℝ := a * (B + M) * 7 * (cfg.N k ^ (-r) + (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D))
    with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hMpos : 0 < 18 * a * M := by rw [hβ]; exact Real.rpow_pos_of_pos hN _
  have hmain := chart_strip_cap hb hN hK hcap hχv (κ 0) (κ 1)
    (ylo := y₀) (yhi := y₀ + D) (ζ₀ := ζ₀) (W := 18 * a * M) (θ := θ) (m := 1) le_rfl
    (by linarith) hζ₀ (by rw [hβ]; push_cast; linarith) hθ0 (by rw [← hβ]; exact hθ) hδχ hdr
    (fun t Y => a * quad2 ref t (etaFun y₀ vv D t Y))
    ((⋃ i ∈ J, L.C h i ×ˢ Icc (0 : ℝ) 1) ∩ goodSet (cfg.b k) ζ₀ Kb) ?_ ?_
  · refine hmain.trans (le_of_eq ?_)
    rw [floorBin_eq_Ico hχ, hβ]
    congr 3
    ring
  · rintro p ⟨hpU, hpt, hph, -⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hpU
    have hiJ := (Finset.mem_filter.mp hi).2
    have hpC : p.1 ∈ L.C h i := hpi.1
    obtain ⟨h3, h0, h1, -⟩ := L.mem_bins hpC
    rw [hiJ.1] at h3 h0 h1
    have hb1lo : y₀ ≤ cfg.b k p.1 1 := by
      have := Int.floor_le (cfg.b k p.1 1 / D); rw [h1, le_div_iff₀ hD] at this; linarith
    have hb1hi : cfg.b k p.1 1 ≤ y₀ + D := by
      have := Int.lt_floor_add_one (cfg.b k p.1 1 / D); rw [h1, div_lt_iff₀ hD] at this
      simp only [y₀]; linarith
    have hη := L.etaFun_mem hpC hχ hD hpt hph hdrift
    rw [hiJ.1] at hη
    have hfit := L.fit hpC hpt
    have hpp : (p.1, p.2) = p := rfl
    rw [hpp] at hfit
    have hval : MvPolynomial.eval ![p.2, basePt (cfg.b k) p 2] (L.G h i) =
        a * quad2 (keySheet (L.G h i) κ χ D a) p.2 (etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2)) := by
      rw [keySheet, quad2_smul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul,
        quad2_sheetCoeff_etaFun (L.degree h i) hD.ne']
    have hdiff : |a * quad2 (keySheet (L.G h i) κ χ D a) p.2 (etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2)) -
        a * quad2 ref p.2 (etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2))| ≤ a * (6 * M) := by
      rw [← mul_sub, abs_mul, abs_of_pos ha, quad2_sub]
      gcongr
      apply abs_quad2_le (fun k' => by simpa using hiJ.2 k')
      · rw [abs_le]; constructor <;> linarith [hpt.1, hpt.2]
      · rw [abs_le]; constructor <;> linarith [hη.1, hη.2]
    rw [hval] at hfit
    have hp0 : basePt (cfg.b k) p 0 = p.2 := rfl
    rw [hp0]
    rw [abs_le] at hfit hdiff
    refine ⟨h3, h0, hb1lo, hb1hi, hpt, hph, ?_, ?_⟩ <;> nlinarith
  · rintro p ⟨hpU, hpt, hph, -⟩ y hy
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hpU
    have hiJ := (Finset.mem_filter.mp hi).2
    have hpC : p.1 ∈ L.C h i := hpi.1
    have hη := L.etaFun_mem hpC hχ hD hpt hph hdrift
    rw [hiJ.1] at hη
    have hp0 : basePt (cfg.b k) p 0 = p.2 := rfl
    have hy0 := hy 0; have hy2 := hy 2
    rw [hp0] at hy0 ⊢
    have hdη := etaFun_sub (y₀ := y₀) (v := vv) hD p.2 (basePt (cfg.b k) p 2) (y 0) (y 2)
    have hvv' : |vv| = |(κ 1 : ℝ) * χ| := by simp only [vv, abs_neg]
    rw [hvv'] at hdη
    have hdη' : |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) - etaFun y₀ vv D (y 0) (y 2)| ≤
        (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) := by
      refine hdη.trans ?_
      have hy2' : |basePt (cfg.b k) p 2 - y 2| ≤ cfg.N k ^ (-r) := hy2
      have hy0' : |p.2 - y 0| ≤ cfg.N k ^ (-r) := hy0
      have hnum : |basePt (cfg.b k) p 2 - y 2| + |(κ 1 : ℝ) * χ| * |p.2 - y 0| ≤
          (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) := by
        nlinarith [abs_nonneg ((κ 1 : ℝ) * χ), abs_nonneg (p.2 - y 0)]
      exact div_le_div_of_nonneg_right hnum (by positivity)
    have hdη1 : (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * D)]; linarith
    have hη2 : |etaFun y₀ vv D (y 0) (y 2)| ≤ 2 := by
      rw [abs_le] at hdη' ⊢
      constructor <;> linarith [hη.1, hη.2, hdη'.1, hdη'.2]
    have hlip := quad2_lipschitz (L := 2) href
      (t := p.2) (t' := y 0) (η := etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2))
      (η' := etaFun y₀ vv D (y 0) (y 2))
      (by rw [abs_le]; constructor <;> linarith [hpt.1, hpt.2])
      (by rw [abs_le] at hy0 ⊢; constructor <;> linarith [hpt.1, hpt.2])
      (by rw [abs_le]; constructor <;> linarith [hη.1, hη.2]) hη2
    rw [← mul_sub, abs_mul, abs_of_pos ha, hθdef]
    have : |p.2 - y 0| + |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) -
        etaFun y₀ vv D (y 0) (y 2)| ≤
        cfg.N k ^ (-r) + (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D) := by linarith
    calc a * |quad2 ref p.2 (etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2)) -
          quad2 ref (y 0) (etaFun y₀ vv D (y 0) (y 2))|
        ≤ a * ((B + M) * (1 + 3 * 2) * (|p.2 - y 0| + |etaFun y₀ vv D p.2 (basePt (cfg.b k) p 2) -
          etaFun y₀ vv D (y 0) (y 2)|)) := by gcongr
      _ ≤ a * ((B + M) * (1 + 3 * 2) * (cfg.N k ^ (-r) +
          (1 + |(κ 1 : ℝ) * χ|) * cfg.N k ^ (-r) / (4 * D))) := by gcongr
      _ = _ := by ring

/-- **Total count of the pieces of one key.** -/
theorem LayerDatum.key_count {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ Kb : ℝ} (hgood : cfg.μ k (goodSet (cfg.b k) ζ₀ Kb)ᶜ = 0) (hζ₀ : 0 ≤ ζ₀) (hKb : 0 ≤ Kb)
    {r v' : ℝ}
    (hcap : JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d r 0 v')
    (hN : 0 < cfg.N k) (hK : 0 ≤ cfg.K k) (hχv : χ = cfg.N k ^ (-v')) (hD : 0 < D)
    (h : Fin 3) (κ : Fin 3 → ℤ)
    (hδχ : (|(κ 0 : ℝ) * χ| + |(κ 1 : ℝ) * χ| + χ + 1) * cfg.N k ^ (-r) ≤ χ / 2)
    (hdr : cfg.N k ^ (-r) ≤ 1 / 2) :
    ((Finset.univ.filter (fun i => L.qp h i = κ)).card : ENNReal) *
      (ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
        cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ))) ≤
      ENNReal.ofReal (3000 * cfg.K k * ((⌈2 * Kb⌉₊ + 1 : ℕ) : ℝ) * χ * (D / 2 + χ / 2 + ζ₀) *
        (cfg.N k ^ (-(0 : ℝ))) ^ cfg.d) *
        cfg.π k (Set.Ico ((κ 0 : ℝ) * χ) (((κ 0 : ℝ) + 1) * χ)) := by
  classical
  have hχ : 0 < χ := by rw [hχv]; exact Real.rpow_pos_of_pos hN _
  set J := Finset.univ.filter (fun i => L.qp h i = κ) with hJdef
  refine (L.card_floor_le hρμ hgood h (κ 0) J (fun i hi => by
    rw [(Finset.mem_filter.mp hi).2])).trans ?_
  have hN0 : cfg.N k ^ (-(0 : ℝ)) = 1 := by simp
  have hmain := chart_strip_cap hb hN hK hcap hχv (κ 0) (κ 1)
    (ylo := (κ 2 : ℝ) * D) (yhi := (κ 2 : ℝ) * D + D) (ζ₀ := ζ₀) (W := 2 * Kb) (θ := 0)
    (m := ⌈2 * Kb⌉₊ + 1) (by omega) (by linarith) hζ₀
    (by rw [hN0]; push_cast; linarith [Nat.le_ceil (2 * Kb)]) le_rfl
    (by rw [hN0]; norm_num) hδχ hdr (fun _ _ => 0)
    ((⋃ i ∈ J, L.C h i ×ˢ Icc (0 : ℝ) 1) ∩ goodSet (cfg.b k) ζ₀ Kb) ?_ ?_
  · refine hmain.trans (le_of_eq ?_)
    rw [floorBin_eq_Ico hχ]
    congr 3
    ring
  · rintro p ⟨hpU, hpt, hph, hpX⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hpU
    have hiJ := (Finset.mem_filter.mp hi).2
    have hpC : p.1 ∈ L.C h i := hpi.1
    obtain ⟨h3, h0, h1, -⟩ := L.mem_bins hpC
    rw [hiJ] at h3 h0 h1
    have hb1lo : (κ 2 : ℝ) * D ≤ cfg.b k p.1 1 := by
      have := Int.floor_le (cfg.b k p.1 1 / D); rw [h1, le_div_iff₀ hD] at this; linarith
    have hb1hi : cfg.b k p.1 1 ≤ (κ 2 : ℝ) * D + D := by
      have := Int.lt_floor_add_one (cfg.b k p.1 1 / D); rw [h1, div_lt_iff₀ hD] at this
      linarith
    rw [abs_le] at hpX
    refine ⟨h3, h0, hb1lo, hb1hi, hpt, hph, ?_, ?_⟩ <;> linarith
  · intro p _ y _
    simp

/-- **Closeness of two layers** along a trajectory of both pieces, in the time-free strip
coordinate `etaOf`. -/
theorem LayerDatum.close {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hρμ : cfg.ρ k ≤ cfg.μ k)
    {ζ₀ : ℝ} (hhor : ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀)
    (hχ : 0 < χ) (hD : 0 < D) (hdrift : ζ₀ + χ ≤ D)
    {h₁ h₂ : Fin 3} (i : Fin (L.np h₁)) (j : Fin (L.np h₂)) (κ : Fin 3 → ℤ)
    (hi : L.qp h₁ i = κ) (hj : L.qp h₂ j = κ) {a δ : ℝ} (ha : 0 < a)
    (hδ : (cfg.N k ^ ε * cfg.N k ^ (-depth h₁) + cfg.N k ^ ε * cfg.N k ^ (-depth h₂) +
      80 * cfg.N k ^ ε * (ζ₀ + χ) / D) / a ≤ δ) :
    ∀ᵐ p ∂L.ρs, p.1 ∈ L.C h₁ i → p.1 ∈ L.C h₂ j →
      etaOf ((κ 2 : ℝ) * D) D (cfg.b k p.1 1) ∈
        closeSet (keySheet (L.G h₁ i) κ χ D a) (keySheet (L.G h₂ j) κ χ D a) δ := by
  have hae : ∀ᵐ p ∂L.ρs, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀ :=
    ae_mono (L.le_rho.trans hρμ) hhor
  filter_upwards [hae] with p hph hp1 hp2
  obtain ⟨-, h0, h1, -⟩ := L.mem_bins hp1
  rw [hi] at h0 h1
  have hb1lo : (κ 2 : ℝ) * D ≤ cfg.b k p.1 1 := by
    have := Int.floor_le (cfg.b k p.1 1 / D); rw [h1, le_div_iff₀ hD] at this; linarith
  have hb1hi : cfg.b k p.1 1 < (κ 2 : ℝ) * D + D := by
    have := Int.lt_floor_add_one (cfg.b k p.1 1 / D); rw [h1, div_lt_iff₀ hD] at this
    linarith
  have hb0lo : (κ 1 : ℝ) * χ ≤ cfg.b k p.1 0 := by
    have := Int.floor_le (cfg.b k p.1 0 / χ); rw [h0, le_div_iff₀ hχ] at this; linarith
  have hb0hi : cfg.b k p.1 0 < ((κ 1 : ℝ) + 1) * χ := by
    have := Int.lt_floor_add_one (cfg.b k p.1 0 / χ); rw [h0, div_lt_iff₀ hχ] at this
    linarith
  have hζ : |cfg.b k p.1 4 - -((κ 1 : ℝ) * χ)| ≤ ζ₀ + χ := by
    rw [abs_le] at hph ⊢; constructor <;> nlinarith
  refine ⟨etaOf_mem hD hb1lo hb1hi, ?_⟩
  refine mem_iInter₂.mpr fun t ht => ?_
  show |quad2 (keySheet (L.G h₁ i) κ χ D a) t (etaOf ((κ 2 : ℝ) * D) D (cfg.b k p.1 1)) -
    quad2 (keySheet (L.G h₂ j) κ χ D a) t (etaOf ((κ 2 : ℝ) * D) D (cfg.b k p.1 1))| ≤ δ
  have hstrip₁ := L.strip h₁ i
  have hstrip₂ := L.strip h₂ j
  rw [hi] at hstrip₁
  rw [hj] at hstrip₂
  have hf₁ := L.fit hp1 ht
  have hf₂ := L.fit hp2 ht
  have hY : basePt (cfg.b k) (p.1, t) 2 = cfg.b k p.1 1 + t * cfg.b k p.1 4 := rfl
  rw [hY] at hf₁ hf₂
  have hs₁ := sheet_fit (L.degree h₁ i) hD hstrip₁ ht hb1lo hb1hi hζ (by linarith) hf₁
  have hs₂ := sheet_fit (L.degree h₂ j) hD hstrip₂ ht hb1lo hb1hi hζ (by linarith) hf₂
  simp only [keySheet, quad2_smul]
  rw [← mul_sub, abs_mul, abs_inv, abs_of_pos ha, inv_mul_le_iff₀ ha]
  rw [div_le_iff₀ ha] at hδ
  have tri := abs_sub_le (quad2 (sheetCoeff (L.G h₁ i) ((κ 2 : ℝ) * D) (-((κ 1 : ℝ) * χ)) D) t
      (etaOf ((κ 2 : ℝ) * D) D (cfg.b k p.1 1))) (hidden (cfg.b k) (p.1, t))
    (quad2 (sheetCoeff (L.G h₂ j) ((κ 2 : ℝ) * D) (-((κ 1 : ℝ) * χ)) D) t
      (etaOf ((κ 2 : ℝ) * D) D (cfg.b k p.1 1)))
  rw [abs_sub_comm (hidden (cfg.b k) (p.1, t))] at tri
  have e80 : 40 * cfg.N k ^ ε * (ζ₀ + χ) / D + 40 * cfg.N k ^ ε * (ζ₀ + χ) / D =
      80 * cfg.N k ^ ε * (ζ₀ + χ) / D := by ring
  linarith

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
