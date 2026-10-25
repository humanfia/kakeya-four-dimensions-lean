/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit f3582cb1, file OriginalSampleWorld.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudget
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryCutBudget
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalFailedSource
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalGlobalPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalGlobalFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalWorldCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalResidualScale
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalGraphLaw
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientWorldChoice
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPieces
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldJetAssembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Lib.K4ContinuousKakeya
open Submission.Obl.k4_scalar_grid_parameter_preparation
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarData

/-- Purely numerical sample budgets construct an actual original world.
All choices and global cuts use the literal frozen data. -/
theorem original_world_of_discovery_budget {D : ScalarData}
    {H Hg : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ Eg : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hprep : D.prepData H θ E₀) (hgraph : D.graphData E₀ L Hg B G Eg)
    (hbase : D.base) (hcaps : D.caps) (hpack : D.packets) (hN : ∀ k, 2 ≤ D.N k)
    (hd : 0 ≤ D.d) (hd₁ : D.d ≤ 1)
    (Cmk : ℝ) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 2 Cmk)
    (M C₁ C J₁ J₂ : ℕ) (hC₁ : 1 ≤ C₁) (hJ₁ : 1 ≤ J₁) (hJ₂ : 1 ≤ J₂)
    (hC₁L : (C₁ : ℝ) ≤ L) (ε δ α cζ : ℝ) (hδ : 0 < δ) :
    ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop,
      ∀ budget : DiscoveryBudget (D.N k) (H k) (Hg k) (D.K k) D.d D.S L B
        (((2 : ℝ) ^ D.T k 1)⁻¹) δ α cζ Cmk T (D.prepMesh hprep k) M C₁ C J₁ J₂,
      δ ≤ (D.toQualificationTable B G Eg).rationalFailureRatio M ε k →
      ∃ w : OriginalJetWorld D H B G Eg M ε k,
        w.K = budget.Knormal ∧ w.ζ = D.N k ^ (-(C : ℝ)) := by
  classical
  have hpoints := (Classical.choose_spec hprep.2).2 2 (by norm_num)
  have hmesh := (Classical.choose_spec hprep.2).1
  intro T hT
  filter_upwards [hgraph.exists_failed_original_row_source hprep hbase hpack hN C₁ J₁ hC₁ hJ₁ hC₁L M ε hδ,
    hprep.prepare_original_global_law hgraph hbase hN T hT,
    hprep.original_global_filling_of_floors hgraph hbase hcaps hN hd hd₁ J₂ C hJ₂ Cmk hCmk hMK T hT,
    hprep.original_world_caps hN T hT, hprep.original_residual_scale hgraph hN T hT,
    hprep.original_raw_spatial_caps hN T hT,
    hgraph.2.2 T hT, hprep.original_density_caps, hpoints] with
      k hsource hglobal hfill hworldcaps hraw hspatial hg hden hp
  intro budget hratio
  obtain ⟨g, E, hω, hE, hEEg, hEbad, hmassE, hcmpE, hphysE, hcoeffE, hinteriorE⟩ := hsource hratio
  let μ := (D.ρ k g).restrict (E₀ k g)
  let old := (D.ρ k g).restrict (Eg k g)
  let ρ := D.N k ^ (-budget.a)
  let b := D.N k ^ (-B)
  let ζ := D.N k ^ (-(C : ℝ))
  let scales := fun i : Fin (C * J₂ + 1) => powerWidth (D.N k) J₂ i
  let u := fun i : Fin (C * J₂ + 1) => upperGridExponent (D.prepMesh hprep k) (budget.a + (i : ℝ) / J₂)
  let β := fun i => D.N k ^ (-u i)
  let Krow := discoveryRowConstant (D.N k) (Hg k) J₁
  let Kh := discoveryTimeConstant (D.N k) (H k) (Hg k) J₁
  let σ := Hg k * D.N k ^ (-L)
  let δc := Krow * (ρ + 2 * b + D.N k ^ (-(C₁ : ℝ)))
  haveI : IsFiniteMeasure (D.ρ k g) := ⟨lt_top_iff_ne_top.mpr (rho_finite hbase k g)⟩
  haveI := (hbase k).2.2.1 g |>.1
  haveI := (hbase k).2.2.1 g |>.2.1
  haveI : IsFiniteMeasure (θ k g) := isFiniteMeasure_of_le (D.ν k g) (hp.2 g).1
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hN₁ : 1 < D.N k := by linarith [hN k]
  have hH : 1 ≤ H k := hprep.1.1 k
  have hHg : 1 ≤ Hg k := hgraph.1.1 k
  have ha : 0 < budget.a := (inv_pos.mpr (by linarith : 0 < T)).trans_le budget.coarse_lower
  have haT : budget.a ≤ T := by
    have hm : 0 ≤ (1 : ℝ) / (D.prepMesh hprep k : ℝ) := by positivity
    linarith [budget.fine_upper, (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  have haB : budget.a ≤ B := by
    have hm : 0 ≤ (1 : ℝ) / (D.prepMesh hprep k : ℝ) := by positivity
    linarith [budget.fine_precision, (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hN₀ _
  have hρ₁ : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁.le (by linarith)
  have hb : 0 < b := Real.rpow_pos_of_pos hN₀ _
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hN₀ _
  have hζ₁ : ζ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁.le (by simp)
  have hη := budget.eta_pos
  have hη₁ := budget.eta_le_one
  have hw (i : Fin (C * J₂ + 1)) :=
    discovery_prepared_scale hN₁.le ha.le (hmesh k).1 hJ₂ (hmesh k).2 i
  have hs (i : Fin (C * J₂ + 1)) : 0 < scales i := Real.rpow_pos_of_pos hN₀ _
  have hsbound (i : Fin (C * J₂ + 1)) : ζ ≤ scales i ∧ scales i ≤ 1 :=
    discovery_scale_bounds hN₁.le hJ₂ i
  have hbβ (i : Fin (C * J₂ + 1)) : b ≤ β i :=
    Real.rpow_le_rpow_of_exponent_le hN₁.le (neg_le_neg ((hw i).2.1.trans budget.fine_precision))
  have hβ (i : Fin (C * J₂ + 1)) : 0 < β i := Real.rpow_pos_of_pos hN₀ _
  have hKrow : 0 ≤ Krow := by dsimp only [Krow, discoveryRowConstant]; positivity
  have hcmp : ∀ p ∈ E, ∀ p' ∈ E, ‖G k g (D.phys k B p) - G k g (D.phys k B p')‖ ≤
      Krow * (‖scalarPosition p - scalarPosition p'‖ + D.N k ^ (-(C₁ : ℝ))) := hcmpE
  have hsmall : ∀ i : Fin (C * J₂ + 1), (1 + 3 * (H k + 1)) * b ≤ ρ * scales i := by
    intro i
    exact budget.point_precision.trans (mul_le_mul_of_nonneg_left (hsbound i).1 hρ.le)
  have hvariation : ∀ i : Fin (C * J₂ + 1),
      (σ + δc * (1 + H k)) * (ρ + 2 * b) + 2 * (1 + 2 * Hg k) * b ≤ ρ * scales i := by
    intro i
    exact budget.variation.trans (mul_le_mul_of_nonneg_left (hsbound i).1 hρ.le)
  obtain ⟨row, P, R, hrowbound, hrowclose, hP, hPE, hR, hRP, hdelete,
    hinter, hlong, hstate, hstrip, hpost, hcoef⟩ :=
    hglobal g budget.a budget.coarse_lower haT budget.coarse_mesh haB β scales
      (fun _ => budget.η⁻¹) (fun _ => budget.η) (fun _ => ENNReal.ofReal budget.η)
      (fun _ => ENNReal.ofReal budget.η) (fun _ => ENNReal.ofReal budget.η)
      (ENNReal.ofReal budget.η) hβ (fun i => (hw i).2.2.1) hs (fun i => (hsbound i).2)
      (fun _ => inv_pos.mpr hη) (fun _ => hη.le) hsmall E hE hEEg
      (hcoeffE budget.a budget.coarse_mesh) Krow (D.N k ^ (-(C₁ : ℝ))) hKrow
      (Real.rpow_nonneg hN₀.le _) hcmp hvariation
  have hRE : R ⊆ E := hRP.trans hPE
  have hREg : R ⊆ Eg k g := hRE.trans hEEg
  have hEgE₀ : Eg k g ⊆ E₀ k g := (hg.2 g).2.1
  have hRprep : R ⊆ E₀ k g := hREg.trans hEgE₀
  have hρθ : (D.ρ k g) univ ≤ ENNReal.ofReal (D.K k) :=
    (original_time_support (D.ν k g) (D.ρ k g) ((hbase k).2.2.1 g).2.2.2.1
      ((hbase k).2.2.1 g).2.2.2.2).2
  have hold : old univ ≤ ENNReal.ofReal budget.Hbig :=
    ((Measure.restrict_le_self univ).trans hρθ).trans (ENNReal.ofReal_le_ofReal budget.original_le)
  have hcurrent : μ E ≤ ENNReal.ofReal budget.Hbig :=
    ((Measure.restrict_le_self E).trans ((measure_mono (subset_univ E)).trans hρθ)).trans
      (ENNReal.ofReal_le_ofReal budget.original_le)
  have hcut : μ (E \ R) ≤ ENNReal.ofReal budget.m₀ := by
    have hcost : μ (E \ R) ≤ discoveryCutBudget (C * J₂ + 1) (H k) budget.η budget.η⁻¹
        (θ k g univ) (old univ) (μ E) (D.π k g univ) := by
      simpa only [discoveryCutBudget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_assoc, μ, old] using hdelete
    exact hcost.trans ((discovery_cut_budget_le budget.one_le_Hbig (by linarith) budget.prep_le hη.le
      (by simp) (by omega) (hp.2 g).2.1 hold hcurrent (by simp)).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using budget.cut_budget)))
  have hfactorFinite : discoveryFirstFactor (Hg k) C₁ J₁ ≠ ∞ := by
    unfold discoveryFirstFactor
    finiteness
  have hfactorPositive : discoveryFirstFactor (Hg k) C₁ J₁ ≠ 0 := by
    intro hz
    change ENNReal.ofReal (δ / (2 * Hg k)) ≤ discoveryFirstFactor (Hg k) C₁ J₁ * μ E at hmassE
    rw [hz, zero_mul] at hmassE
    have hpos : 0 < ENNReal.ofReal (δ / (2 * Hg k)) := ENNReal.ofReal_pos.mpr (by positivity)
    exact not_le_of_gt hpos hmassE
  have hsourcefloor : ENNReal.ofReal (2 * budget.m₀) ≤ μ E := by
    have hh := budget.source_budget.trans hmassE
    change ENNReal.ofReal (2 * budget.m₀) * discoveryFirstFactor (Hg k) C₁ J₁ ≤
      discoveryFirstFactor (Hg k) C₁ J₁ * μ E at hh
    rw [mul_comm (discoveryFirstFactor (Hg k) C₁ J₁)] at hh
    exact (ENNReal.mul_le_mul_iff_left hfactorPositive hfactorFinite).mp hh
  have hRfloor : ENNReal.ofReal budget.m₀ ≤ μ R := by
    have hpartition : μ E = μ (E \ R) + μ R := by
      simpa only [inter_eq_right.mpr hRE] using (measure_sdiff_add_inter E hR).symm
    have hh := hsourcefloor.trans (hpartition.le.trans (add_le_add hcut le_rfl))
    have hdouble : ENNReal.ofReal (2 * budget.m₀) =
        ENNReal.ofReal budget.m₀ + ENNReal.ofReal budget.m₀ := by
      rw [show 2 * budget.m₀ = budget.m₀ + budget.m₀ by ring,
        ENNReal.ofReal_add budget.mass_pos.le budget.mass_pos.le]
    have hh' : ENNReal.ofReal budget.m₀ + ENNReal.ofReal budget.m₀ ≤ μ R + ENNReal.ofReal budget.m₀ := by
      simpa only [hdouble, add_comm] using hh
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hh'
  have hdomR : μ.restrict R ≤ ENNReal.ofReal (H k) • (θ k g).prod volume :=
    (Measure.restrict_le_self : μ.restrict R ≤ μ) |>.trans (hden g).1
  obtain ⟨q, hq, hprob, hmassq⟩ := Zoom.exists_dense_coefficient_world (θ k g) μ ρ R hR
    (hp.2 g).2.1 hdomR budget.mass_pos hRfloor
  have hmassqGraph : ENNReal.ofReal (budget.m₀ / 2) * θ k g {l | cell ρ l.2 = q} ≤
      old (R ∩ {p | cell ρ p.1.2 = q}) := by
    exact hmassq.trans_eq (D.original_graph_measure_on_retained k g hR hREg hEgE₀ _)
  have hcoeffBound : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H k :=
    fun p hpR => ((hp.2 g).2.2.2.1 p (hRprep hpR)).2
  have htime : ∀ p ∈ R, p.2 ∈ Icc (0 : ℝ) 1 :=
    fun p hpR => ((hp.2 g).2.2.2.1 p (hRprep hpR)).1
  have hgraphBound : ∀ p ∈ R, ∀ e, |G k g (D.phys k B p) e| ≤ Hg k :=
    fun p hpR => ((hg.2 g).2.2.1 p (hREg hpR)).1
  have hgraphError : ∀ p ∈ R,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (D.phys k B p) 0 -
        G k g (D.phys k B p) 1 * p.1.2 1| ≤ σ :=
    fun p hpR => ((hg.2 g).2.2.1 p (hREg hpR)).2
  have hcoefficientPositive (v : ℝ) (hv : ∃ j : ℕ, v = (j : ℝ) / (D.prepMesh hprep k : ℝ))
      (p : ScalarIncidence) (hpR : p ∈ R) :
      μ {p' | D.coeff k v p'.1 = D.coeff k v p.1} ≠ 0 := by
    have hh := hcoeffE v hv p (hRE hpR)
    intro hz
    exact hh (measure_mono_null (fun _ h => h.2) hz)
  have hmassqPositive : old (R ∩ {p | cell ρ p.1.2 = q}) ≠ 0 := by
    have hpos : 0 < ENNReal.ofReal (budget.m₀ / 2) * θ k g {l | cell ρ l.2 = q} :=
      pos_iff_ne_zero.mpr (mul_ne_zero
        (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos budget.mass_pos (by norm_num)))) hq)
    exact ne_of_gt (hpos.trans_le hmassqGraph)
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hmassqPositive
  have hpq : cell ρ p₀.1.2 = q := hp₀.2
  have hqPositive : μ {p | cell ρ p.1.2 = q} ≠ 0 := by
    have hh := hcoefficientPositive budget.a budget.coarse_mesh p₀ hp₀.1
    change μ {p | cell ρ p.1.2 = cell ρ p₀.1.2} ≠ 0 at hh
    simpa only [hpq] using hh
  have hpalette : D.π k g (scalarVelocityBin ρ (q 1)) ≠ 0 := by
    have hcap := (hspatial g budget.a budget.a budget.coarse_lower haT budget.coarse_lower haT
      budget.coarse_mesh budget.coarse_mesh).1 q hqPositive |>.2
    intro hz
    rw [hz, mul_zero] at hcap
    exact hq (le_antisymm hcap zero_le)
  have hui (i : Fin (C * J₂ + 1)) : T⁻¹ ≤ u i ∧ u i ≤ T ∧
      ∃ j : ℕ, u i = (j : ℝ) / (D.prepMesh hprep k : ℝ) :=
    ⟨budget.coarse_lower.trans (hw i).1, (hw i).2.1.trans budget.fine_upper,
      upperGridExponent_on_grid _ _⟩
  have hpostGraph (i : Fin (C * J₂ + 1)) (e : Zoom.OriginalPosteriorRecord) :
      R ∩ Zoom.posteriorEntryRecord ρ b (scales i) ⁻¹' {e} = ∅ ∨
        ENNReal.ofReal budget.η * old ((fun p => cell b (scalarPosition p)) ⁻¹' {e.2.1}) *
          D.π k g (scalarVelocityBin ρ e.2.2) <
            old (R ∩ Zoom.posteriorEntryRecord ρ b (scales i) ⁻¹' {e}) := by
    rcases hpost i e with hempty | hf
    · exact Or.inl hempty
    · exact Or.inr (hf.trans_eq (D.original_graph_measure_on_retained k g hR hREg hEgE₀ _))
  have hcoefGraph (i : Fin (C * J₂ + 1)) (z : Fin 3 → ℤ) (B' : Fin 5 → ℤ) :
      R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ (β i) q B') (scales i) z = ∅ ∨
        ENNReal.ofReal (scales i / budget.η⁻¹) * θ k g (Zoom.parameterPiece ρ (β i) q B') <
          old (R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ (β i) q B') (scales i) z) := by
    rcases hcoef i q B' z with hempty | hf
    · exact Or.inl hempty
    · exact Or.inr (hf.trans_eq (D.original_graph_measure_on_retained k g hR hREg hEgE₀ _))
  have hrawScales (i : Fin (C * J₂ + 1)) :
      ∃ raw : Zoom.OriginalResidualScale old (θ k g) (D.π k g) R (Eg k g) ρ b (scales i) (H k) q,
        ∀ Hrow Lrow : ℝ, raw.listBound Hrow Lrow =
          (Hg k / budget.η + 2) *
            ((budget.η⁻¹ * H k ^ 3 * (H k + 2) ^ 2 / budget.η) *
              (2 * (7 + Hrow + 2 * Lrow) + 2)) :=
    hraw g (u i) (hui i).1 (hui i).2.1 (hui i).2.2 R hREg ρ (scales i)
      budget.η⁻¹ budget.η budget.η hρ (hs i) (hw i).2.2.1 (hw i).2.2.2
      (inv_pos.mpr hη) hη hη q hpalette
      (hcoefficientPositive (u i) (hui i).2.2) (fun p hpR => hinter p hpR i)
      (hpostGraph i) (hcoefGraph i)
  choose rawScales hrawFormula using hrawScales
  obtain ⟨pick, _, _, hpick⟩ := exists_discovery_piece_selector hN₁ ha.le (D.prepMesh hprep k) J₂ C
    (hmesh k).1 hJ₂ (hmesh k).2
  let f := fun r => u (pick r)
  have hf : ∀ r, ζ ≤ r → r ≤ 1 → T⁻¹ ≤ f r ∧ f r ≤ T ∧
      ∃ j : ℕ, f r = (j : ℝ) / (D.prepMesh hprep k : ℝ) := fun r _ _ => hui (pick r)
  have hfwidth : ∀ r, ζ ≤ r → r ≤ 1 →
      D.N k ^ (-f r) ≤ ρ * r ∧ ρ * r ≤ (H k * D.N k ^ (1 / (J₂ : ℝ))) * D.N k ^ (-f r) :=
    fun r hr hr₁ => ⟨(hpick r hr hr₁).1, (hpick r hr hr₁).2.1⟩
  have hfpositive : ∀ r, ζ ≤ r → r ≤ 1 → ∀ p ∈ R,
      μ {p' | cell (D.N k ^ (-f r)) p'.1.2 = cell (D.N k ^ (-f r)) p.1.2} ≠ 0 := by
    intro r hr hr₁ p hpR
    exact hcoefficientPositive (f r) (hf r hr hr₁).2.2 p hpR
  have hfinter : ∀ r, ζ ≤ r → r ≤ 1 → ∀ p ∈ R,
      ENNReal.ofReal budget.η * θ k g {l | cell (D.N k ^ (-f r)) l.2 = cell (D.N k ^ (-f r)) p.1.2} ≤
        θ k g {l | cell ρ l.2 = cell ρ p.1.2 ∧
          cell (D.N k ^ (-f r)) l.2 = cell (D.N k ^ (-f r)) p.1.2} :=
    fun r _ _ p hpR => hinter p hpR (pick r)
  have hQ₂ : 1 ≤ D.N k ^ (1 / (J₂ : ℝ)) := Real.one_le_rpow hN₁.le (by positivity)
  have hAcoarse : 1 ≤ H k * D.N k ^ (1 / (J₂ : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hQ₂ (by linarith : 0 ≤ H k)
    linarith
  obtain ⟨caps, hcapsH, hcapsA, hcapsη, hcapsβ⟩ :=
    hworldcaps g budget.a budget.coarse_lower haT budget.coarse_mesh R hRprep ζ
      (H k * D.N k ^ (1 / (J₂ : ℝ))) budget.η hζ hζ₁ hAcoarse hη f hf hfwidth
      hfpositive hfinter q hqPositive
  have hArow : ∀ v, 5 + |row v 0| + |row v 1| ≤ 5 + 2 * Hg k := by
    intro v
    linarith [hrowbound v 0, hrowbound v 1]
  obtain ⟨filling, hfillRow, hfillQ, hfillK, hfillA, hfillB⟩ :=
    hfill g budget.a budget.τ budget.coarse_lower budget.fine_upper budget.tau_lower budget.tau_upper
      P R hP hR hRP (hPE.trans hEEg) hbβ
      (fun i j p hpR => hphysE (u i) (u j) (hui i).2.2 (hui j).2.2 p (hRE hpR))
      budget.Kbase budget.Kgeom budget.Lfill budget.η budget.η (ENNReal.ofReal budget.η)
      budget.Kbase_pos budget.Kgeom_pos budget.Lfill_pos hη hη budget.Kbase_density budget.Kbase_prior
      budget.filling_budget budget.filling_le (ne_of_gt (ENNReal.ofReal_pos.mpr hη)) ENNReal.ofReal_ne_top
      budget.angular_budget hstate row hlong hstrip (5 + 2 * Hg k) hArow
      budget.hereditary_budget budget.overlap_budget
  have hcenter : ∀ e, |(Zoom.center ρ q).2 e| ≤ H k + 1 := by
    intro e
    have he := (norm_le_pi_norm (p₀.1.2 - leftCorner ρ (cell ρ p₀.1.2)) e).trans
      (norm_sub_leftCorner_le hρ p₀.1.2)
    rw [hpq] at he
    change |p₀.1.2 e - (Zoom.center ρ q).2 e| ≤ ρ at he
    have htri := abs_sub_le ((Zoom.center ρ q).2 e) (p₀.1.2 e) (0 : ℝ)
    simp only [sub_zero, abs_sub_comm ((Zoom.center ρ q).2 e)] at htri
    linarith [hcoeffBound p₀ hp₀.1 e]
  have hζrow : D.N k ^ (-(C₁ : ℝ)) ≤ ρ :=
    Real.rpow_le_rpow_of_exponent_le hN₁.le (neg_le_neg budget.row_precision)
  have hρζ : ρ ≤ ζ := Real.rpow_le_rpow_of_exponent_le hN₁.le (neg_le_neg budget.coarse_floor)
  have hbρ : b ≤ ρ := Real.rpow_le_rpow_of_exponent_le hN₁.le (neg_le_neg haB)
  have hcompareR : ∀ p ∈ R, ∀ p' ∈ R,
      |G k g (D.phys k B p) 1 - G k g (D.phys k B p') 1| ≤
        Krow * (‖scalarPosition p - scalarPosition p'‖ + ρ) := by
    intro p hpR p' hpR'
    exact (norm_le_pi_norm (G k g (D.phys k B p) - G k g (D.phys k B p')) 1).trans
      ((hcmp p (hRE hpR) p' (hRE hpR')).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hζrow) hKrow))
  have hphys (p : ScalarIncidence) : D.phys k B p = cell b (scalarPosition p) := rfl
  have hlistBudget (i : Fin (C * J₂ + 1)) :
      (rawScales i).listBound (Hg k) (12 * Kh ^ 2) ≤
        (discoveryListBudget (D.N k) (H k) (Hg k) budget.η J₁ : ℝ) := by
    rw [hrawFormula i]
    change discoveryListFormula (D.N k) (H k) (Hg k) budget.η J₁ ≤
      (⌈discoveryListFormula (D.N k) (H k) (Hg k) budget.η J₁ + 1⌉₊ : ℝ)
    exact (by linarith : discoveryListFormula (D.N k) (H k) (Hg k) budget.η J₁ ≤
      discoveryListFormula (D.N k) (H k) (Hg k) budget.η J₁ + 1).trans (Nat.le_ceil _)
  have hdiam : (1 + 3 * (H k + 1)) * b / ρ ≤ ζ :=
    (div_le_iff₀ hρ).mpr (by nlinarith only [budget.point_precision])
  let primitive : Zoom.OriginalWorldSelectionInput old (θ k g) (D.π k g) R (Eg k g) ρ b
      (H k) (H k + 1) Krow (Hg k) (D.N k ^ (1 / (J₂ : ℝ))) ζ σ q (G k g) := {
    measurable_R := hR
    sub := hREg
    rho_pos := hρ
    rho_le_one := hρ₁
    b_pos := hb
    one_le_H := hH
    one_le_Hc := by linarith
    Krow_nonneg := hKrow
    Hrow_nonneg := by linarith
    one_le_A := hQ₂
    zeta_pos := hζ
    zeta_le_one := hζ₁
    rho_le_zeta := hρζ
    diameter_budget := hdiam
    error_budget := budget.residual_precision
    coeff_bound := hcoeffBound
    time_mem := htime
    center_bound := hcenter
    row_bound := fun p hpR _ => by simpa only [hphys] using hgraphBound p hpR 1
    row_compare := fun p hpR _ p' hpR' _ => by simpa only [hphys] using hcompareR p hpR p' hpR'
    graph_error := fun p hpR => by simpa only [hphys] using hgraphError p hpR
    n := C * J₂ + 1
    one_le_n := by omega
    s := powerWidth (D.N k) J₂
    K := fun _ => discoveryListBudget (D.N k) (H k) (Hg k) budget.η J₁
    first_scale := by simp [powerWidth]
    scale_pos := fun _ => Real.rpow_pos_of_pos hN₀ _
    scale_floor := fun i hi => (hsbound ⟨i, hi⟩).1
    ratio := fun i _ => (powerWidth_ratio hN₀ J₂ i).le
    last_scale := powerWidth_last (D.N k) hJ₂ C
    raw := rawScales
    list_budget := hlistBudget
  }
  have hdomOld : old ≤ ENNReal.ofReal (H k) • (θ k g).prod volume :=
    (Measure.restrict_mono_set (D.ρ k g) hEgE₀).trans (hden g).1
  have hAC : 9 * caps.H ^ 2 * caps.A ^ 4 ≤ budget.Knormal := by
    rw [hcapsH, hcapsA]
    have hnum : 0 ≤ 9 * H k ^ 2 * (H k * D.N k ^ (1 / (J₂ : ℝ))) ^ 4 := by positivity
    have hh := mul_le_mul_of_nonneg_left hη₁ hnum
    simp only [mul_one] at hh
    exact ((le_div_iff₀ hη).mpr hh).trans budget.cap_budget
  have hBC : 9 * caps.H ^ 2 * caps.A ^ 4 / caps.η ≤ budget.Knormal := by
    simpa only [hcapsH, hcapsA, hcapsη] using budget.cap_budget
  have hSS : filling.supportBound (Hg k) ≤ budget.Knormal := by
    simpa only [Zoom.GlobalWorldFilling.supportBound, hfillK, hfillQ] using budget.support_budget
  have hcoarse : ∀ p ∈ R, cell ρ p.1.2 = q →
      |filling.row (assignedCell ρ b p) 1 - G k g (cell b (scalarPosition p)) 1| ≤ δc := by
    intro p hpR _
    simpa only [hfillRow, assignedCell, assignedPosition, abs_sub_comm, hphys] using
      hrowclose p (hRE hpR) 1
  have hsuppPrecision : ∀ v,
      2 * (δc + 4 * Zoom.worldRowConstant (H k + 1) Krow ^ 2 * ρ) +
        (1 + |filling.row v 0| + |filling.row v 1|) * b / ρ ≤ ζ := by
    intro v
    have hbound : 1 + |filling.row v 0| + |filling.row v 1| ≤ 1 + 2 * Hg k := by
      rw [hfillRow]
      linarith [hrowbound v 0, hrowbound v 1]
    have hh : (1 + |filling.row v 0| + |filling.row v 1|) * b / ρ ≤ (1 + 2 * Hg k) * b / ρ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound hb.le) hρ.le
    exact (add_le_add le_rfl hh).trans budget.support_precision
  let input : Zoom.OriginalJetWorldInput D H B G Eg M ε k := {
    g := g
    μ := old
    θ := θ k g
    π := D.π k g
    finite_mu := inferInstance
    finite_theta := inferInstance
    finite_pi := inferInstance
    R := R
    ρ := ρ
    Hc := H k + 1
    Krow := Krow
    Hrow := Hg k
    A := D.N k ^ (1 / (J₂ : ℝ))
    ζ := ζ
    σ := σ
    q := q
    primitive := primitive
    caps := caps
    filling := filling
    b_le_rho := hbρ
    Knormal := budget.Knormal
    U := H k
    δ := budget.m₀ / 2
    P := budget.P
    δc := δc
    one_le_Knormal := budget.one_le_Knormal
    U_pos := by linarith
    delta_pos := div_pos budget.mass_pos (by norm_num)
    P_pos := budget.P_pos
    density_cap := hdomOld
    coefficient_positive := hq
    mass_floor := hmassqGraph
    selection_cost := by
      simpa only [primitive, Finset.prod_const, Finset.card_range] using budget.selection_budget
    mass_budget := budget.mass_budget
    row_budget := budget.row_budget
    row_compare_budget := budget.row_compare_budget
    residual_budget := budget.residual_budget
    absolute_cap_budget := hAC
    conditional_cap_budget := hBC
    support_budget := hSS
    coarse_compare := hcoarse
    support_precision := hsuppPrecision
    failed := fun p hpR => hEbad (hRE hpR)
    interior := fun p hpR => hinteriorE p (hRE hpR)
    graph_margin := budget.graph_margin
    row_margin := budget.row_margin
  }
  obtain ⟨w, hwK, hwζ⟩ := input.exists_world hd hd₁
  exact ⟨w, hwK, hwζ⟩

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
