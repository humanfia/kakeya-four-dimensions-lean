import Submission.Obl.k4_physical_parent_potential_candidates.AssignedFilling
import Submission.Obl.k4_physical_parent_potential_candidates.CellCatalogue
import Submission.Obl.k4_physical_parent_potential_candidates.GroupFamily
import Submission.Obl.k4_physical_parent_potential_candidates.HeavyGroupBudget

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya
open Submission.Lib.K4OriginalCellSampling.Sampling
open scoped ENNReal

noncomputable section

/-- Physical own-intercept fits, fine-state breadth, and the joint census
produce an original heavy intercept bin at the scalar support exponent. -/
theorem exists_original_heavy_intercept_bin
    {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν]
    (A Aold : Set Λ) (hA : MeasurableSet A) (hAAold : A ⊆ Aold)
    (h t0 ε p w θ Lip K δ C d : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (hp : 0 < p) (hw : 0 < w)
    (hεp : ε ≤ p) (hεw : ε ≤ w)
    (hθ : θ ≤ w) (hLip : 0 ≤ Lip) (hmesh : Lip*p ≤ w)
    (hK : 2 ≤ K) (hδ : 0 < δ) (hC : 0 < C) (hMK : FiniteMK 3 C)
    (hprior : 0 < ν.real Aold)
    (base : Λ → EuclideanSpace ℝ (Fin 3))
    (velocity : Λ → EuclideanSpace ℝ (Fin 2))
    (hbase : Measurable base) (hvelocity : Measurable velocity)
    (B : ℝ) (hB : 0 ≤ B) (hbaseB : ∀ l ∈ A, ‖base l‖ ≤ B)
    (hvel : ∀ l ∈ A, ‖velocity l‖ ≤ K)
    (z : (Λ × ℝ) → EuclideanSpace ℝ (Fin 3)) (hz : Measurable z)
    (hfirst : ∀ e, z e 0 = (e.2-t0)/h)
    (haffine : ∀ e, z e = base e.1 + ((e.2-t0)/h) • lift (velocity e.1))
    (X : (Λ × ℝ) → ℝ) (hX : Measurable X)
    (intercept : Λ → ℝ) (hintercept : Measurable intercept)
    (P : (Fin 3 → ℝ) → ℝ)
    (S : Set (Λ × ℝ)) (hS : MeasurableSet S) (hSA : S ⊆ A ×ˢ Icc t0 (t0+h))
    (hfloor : h*ν.real Aold/K ≤ (ν.prod volume).real S)
    (hfit : ∀ e ∈ S, |X e - P (fun i => z e i) - intercept e.1| ≤ θ)
    (hpol : ∀ e ∈ S, ∀ f ∈ S,
      |P (fun i => z e i) - P (fun i => z f i)| ≤
        Lip*‖(fun i => z e i) - (fun i => z f i)‖)
    (hstrip : ∀ k : (Fin 3 → ℤ) × ℤ,
      ∀ (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      ((ν.prod volume).restrict S)
        {e | ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋) = k ∧
          |inner ℝ n (velocity e.1)-t| ≤ δ} ≤
        ENNReal.ofReal ((1:ℝ)/1000000000000) * ((ν.prod volume).restrict S)
          {e | ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋) = k})
    (hcensusFinite : Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k})
    (hcensus : (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
      ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard : ℝ) ≤ K/(p^3*w^d)) :
    ∃ g : ℤ,
      h*ν.real Aold*(δ^2/(1+K)^3/8)*w^d /
          (7962624*(1000*C)^2*K^5) ≤
        ((ν.prod volume).restrict S).real {e | ⌊intercept e.1/w⌋ = g} := by
  classical
  let μ := (ν.prod volume).restrict S
  have hμfin : μ univ < ⊤ := by
    apply lt_of_le_of_lt (original_block_mass_le ν A t0 h S hSA)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν A)
  letI : IsFiniteMeasure μ := ⟨hμfin⟩
  let state (e : Λ × ℝ) := ((fun i : Fin 3 => ⌊z e i/ε⌋), ⌊X e/ε⌋)
  have hstate : Measurable state := by dsimp [state]; fun_prop
  let bin (l : Λ) : ℤ := ⌊intercept l/w⌋
  have hbin : Measurable bin := Int.measurable_floor.comp (hintercept.div_const w)
  let group (e : Λ × ℝ) : ℤ := bin e.1
  have hgroup : Measurable group := hbin.comp measurable_fst
  obtain ⟨hpairFinite, hpairCount⟩ := restricted_assigned_intercept_census S S (Subset.refl S)
    (fun e i => z e i) X (fun e => intercept e.1) P ε p w θ Lip
    hε hp hw hεp hLip hθ hmesh hfit hpol hcensusFinite
  let pairs := hpairFinite.toFinset
  let groups : Finset ℤ := pairs.image Prod.fst
  let cells (g : ℤ) : Finset (Fin 3 → ℤ) :=
    (pairs.filter (fun k => k.1 = g)).image Prod.snd
  have hpairmem (e : Λ × ℝ) (he : e ∈ S) :
      (group e, assignedBaseCode ε p z e) ∈ pairs := by
    exact hpairFinite.mem_toFinset.mpr ⟨e, he, rfl⟩
  have hgroups (e : Λ × ℝ) (he : e ∈ S) : group e ∈ groups :=
    Finset.mem_image.mpr ⟨_, hpairmem e he, rfl⟩
  have hpairsCard : (pairs.card : ℝ) ≤ 243*K/(p^3*w^d) := by
    have hhcard : (pairs.card : ℝ) ≤
        243*(({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard : ℝ) := by
      simpa only [pairs, Set.ncard_eq_toFinset_card _ hpairFinite, Nat.cast_mul,
        Nat.cast_ofNat] using (show (({k : ℤ × (Fin 3 → ℤ) | ∃ e ∈ S,
          (⌊intercept e.1/w⌋, stateAssignedBase ε p
            ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋)) = k}).ncard : ℝ) ≤
          (243:ℝ)*(({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
            ((fun i => ⌊z e i/p⌋), ⌊X e/w⌋) = k}).ncard : ℝ) by exact_mod_cast hpairCount)
    apply hhcard.trans
    calc
      _ ≤ 243*(K/(p^3*w^d)) := mul_le_mul_of_nonneg_left hcensus (by norm_num)
      _ = _ := by ring
  have hbudget : (∑ g ∈ groups, ((cells g).card : ℝ)) ≤ 243*K/(p^3*w^d) :=
    (catalogue_group_cell_budget pairs groups).trans hpairsCard
  obtain ⟨menu, hmenuCard, hmenu⟩ := fine_intercept_menus S (fun e i => z e i) X
    (fun e => intercept e.1) P ε w θ Lip hε hw hLip hεw hθ
    ((mul_le_mul_of_nonneg_left hεp hLip).trans hmesh) hfit hpol
  let f : ENNReal := ENNReal.ofReal ((1:ℝ)/10000)
  have hf0 : f ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hftop : f ≠ ⊤ := ENNReal.ofReal_ne_top
  let G (g : ℤ) := sourceGroupKeep μ state S group f g
  have hGm (g : ℤ) : MeasurableSet (G g) :=
    Submission.Lib.K4StateFractionKeep.measurableSet_fractionKeep hstate
      (hS.inter (hgroup (measurableSet_singleton g))) f
  have hGS (g : ℤ) : G g ⊆ S := fun e he => he.1.1
  have hGgroup (g : ℤ) : ∀ e ∈ G g, group e = g := fun e he => he.1.2
  let prior (g : ℤ) := ν.real (lineBin A bin g)
  let mass (g : ℤ) := μ.real (G g)
  have hGA (g : ℤ) : G g ⊆ lineBin A bin g ×ˢ Icc t0 (t0+h) := by
    intro e he
    exact ⟨⟨(hSA (hGS g he)).1, hGgroup g e he⟩, (hSA (hGS g he)).2⟩
  have hraw (g : ℤ) : μ.restrict (G g) = (ν.prod volume).restrict (G g) :=
    Measure.restrict_restrict_of_subset (hGS g)
  have hmassRaw (g : ℤ) : mass g = ((ν.prod volume).restrict (G g)).real univ := by
    rw [← hraw g]
    simp only [mass, measureReal_def, Measure.restrict_apply_univ]
  have hmassSum : h*ν.real Aold/(4*K) ≤ ∑ g ∈ groups, mass g := by
    have hret := group_fraction_keep_real_budget μ state hstate S hS group hgroup
      menu 9 hmenuCard hmenu groups hgroups ((1:ℝ)/10000) (by norm_num)
    have hμS : μ.real S = (ν.prod volume).real S := by
      simp only [μ, measureReal_def, Measure.restrict_apply' hS, inter_self]
    have hμuniv : μ.real univ = (ν.prod volume).real S := by
      simp only [μ, measureReal_def, Measure.restrict_apply_univ]
    rw [hμS, hμuniv] at hret
    apply quarter_reference_after_retention hK (by positivity) hfloor
      (show (ν.prod volume).real S ≤ (ν.prod volume).real S + (h*ν.real Aold)/K^2 by
        exact le_add_of_nonneg_right (by positivity))
    convert hret using 1 <;> norm_num <;> ring
  have hpriorSum : ∑ g ∈ groups, prior g ≤ ν.real Aold :=
    lineBin_prior_sum_le ν hA hAAold hbin groups
  have hfill (g : ℤ) (hg : g ∈ groups) (hmg : 0 < mass g)
      (hefficient : h/(8*K)*prior g ≤ mass g) :
      (δ^2/(1+K)^3/8)/(4096*(1000*C)^2*K^3*p^3) ≤ ((cells g).card : ℝ) := by
    let Agroup := lineBin A bin g
    have hAgroup : MeasurableSet Agroup := measurableSet_lineBin hA hbin g
    have hAgroupSub : Agroup ⊆ A := inter_subset_left
    let equiv := (cells g).equivFin
    let code : Fin (cells g).card → Fin 3 → ℤ := fun i => (equiv.symm i).1
    have hcode : Function.Injective code := fun i j hij => equiv.symm.injective (Subtype.ext hij)
    have hcover (e : Λ × ℝ) (he : e ∈ G g) : assignedBaseCode ε p z e ∈ Set.range code := by
      have hmem : assignedBaseCode ε p z e ∈ cells g := by
        apply Finset.mem_image.mpr
        refine ⟨(g, assignedBaseCode ε p z e), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        exact ⟨by simpa only [← hGgroup g e he] using hpairmem e (hGS g he), rfl⟩
      exact ⟨equiv ⟨_, hmem⟩, by simp only [code, Equiv.symm_apply_apply]⟩
    obtain ⟨R, hR⟩ := finite_assignedUnitCell_ball code
    have hstripG (i : Fin (cells g).card) (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
        (hn : ‖n‖ = 1) :
        (((ν.prod volume).restrict (G g)).restrict
          {e | e.1 ∈ Agroup ∧ assignedBaseCode ε p z e = code i})
          {e | |inner ℝ n (velocity e.1)-t| ≤ δ} ≤
        (1/1000:ENNReal)*((ν.prod volume).restrict (G g))
          {e | e.1 ∈ Agroup ∧ assignedBaseCode ε p z e = code i} := by
      have hQ : MeasurableSet {e : Λ × ℝ | |inner ℝ n (velocity e.1)-t| ≤ δ} :=
        measurableSet_le (by fun_prop) measurable_const
      have hT : MeasurableSet (S ∩ group ⁻¹' {g}) :=
        hS.inter (hgroup (measurableSet_singleton g))
      have hr := original_retained_group_coarse_ratio ν S state hstate
        (S ∩ group ⁻¹' {g}) hT inter_subset_left Agroup hAgroup
        (fun e he => ⟨(hSA he.1).1, he.2⟩) f hf0 hftop
        (stateAssignedBase ε p) (code i) _ hQ
        (ENNReal.ofReal ((1:ℝ)/1000000000000))
        (fun k => hstrip k n t hn)
      have hratio : ENNReal.ofReal ((1:ℝ)/1000000000000)/f ≤ (1/1000:ENNReal) := by
        dsimp only [f]
        rw [← ENNReal.ofReal_div_of_pos (by norm_num)]
        rw [show (1/1000:ENNReal) = ENNReal.ofReal ((1:ℝ)/1000) by
          norm_num [ENNReal.ofReal_div_of_pos]]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      exact hr.trans (mul_le_mul' hratio le_rfl)
    have hMKbound := assigned_original_filling ν Agroup hAgroup h t0 ε p K δ C
      hh hε hp hεp (by linarith) hδ hC.le hMK base velocity hbase hvelocity
      B hB (fun l hl => hbaseB l (hAgroupSub hl)) (fun l hl => hvel l (hAgroupSub hl))
      z hz hfirst haffine (G g) (hGm g) (hGA g) code hcode hcover R hR hstripG
    rw [← hmassRaw g] at hMKbound
    have hupperENN := original_block_mass_le ν Agroup t0 h (G g) (hGA g)
    have hupperReal : mass g ≤ h*prior g := by
      rw [hmassRaw g]
      have hr := ENNReal.toReal_mono (by finiteness) hupperENN
      simpa only [prior, Agroup, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le, measureReal_def] using hr
    have hpriorPos : 0 < prior g := by
      have hp0 : 0 ≤ prior g := measureReal_nonneg
      by_contra hnot
      have hz : prior g = 0 := le_antisymm (le_of_not_gt hnot) hp0
      rw [hz, mul_zero] at hupperReal
      exact (not_le_of_gt hmg) hupperReal
    exact original_cubic_cell_count_floor (by positivity) hh hp (by linarith)
      (by positivity : 0 < 1000*C) hpriorPos hefficient hMKbound
  obtain ⟨g, hg, hmg, hefficient, hheavy⟩ := three_dimensional_heavy_group_selection
    groups mass prior cells hh (by linarith) (by positivity : 0 < 1000*C) hp hw
    (by positivity : 0 < δ^2/(1+K)^3/8) hprior
    (fun g hg => measureReal_nonneg) (fun g hg => measureReal_nonneg)
    hpriorSum hmassSum hfill hbudget
  refine ⟨g, hheavy.trans ?_⟩
  exact measureReal_mono (fun e he => hGgroup g e he)

end

end Submission.Obl.k4_physical_parent_potential_candidates
