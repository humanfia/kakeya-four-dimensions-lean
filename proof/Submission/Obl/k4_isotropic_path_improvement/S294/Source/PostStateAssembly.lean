-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.PostStateAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.StagesAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildFailureQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Glue

/-!
# From the child states to the stage conclusion (session x1082)

After the states of all children at the child level are built on the root survivors (`E2`,
`child_states_of_records`), the remaining steps of a sample are:

1. the whole ancestor-graph-code regularity cut (`U a` for each active ancestor `a`, keeping a
   `Pfac⁻¹` fraction of each ancestor slice), assembled with exact slices
   (`assemble_same_level_whole_cuts`); states survive by `StateClauses.restrict_coarser_code`;
2. the whole bad-child pruning of native qualification failures relative to the regularity
   reference `Eref a = E2(γ a) ∩ F_a ∩ code_a⁻¹(U a)` (`discard_failure_heavy_children`,
   ratio `1/10000`);
3. the density `M(E5)/2 ≥ 1/K`, and at every dense child the literal child clauses: states
   restricted to the whole codes, rows by `rowClauses_of_readout` with the lists on
   `Er = Eref (anc b) ∩ F_b`, qualification by `child_qual_clauses_of_original_native_failure_ratio`
   on the same `Er`, caps restricted from the root survivors.

`post_state_assembly` takes the regularity mass bound, the lists, the failure bound and the caps
as hypotheses; they are the outputs of the regularity/qualification and cap producers.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual)
open Parent.Qualification.Jets2
open scoped ENNReal BigOperators

noncomputable section

/-- The ancestor's clock code at the graph mesh. -/
abbrev ancCode {W : ℕ} (Nk : ℝ) (p : PathData W) (a : Fin p.C) (graphMesh : ℝ) : Ev → (Fin 4 → ℤ) :=
  clockParentCode p a (Parent.SignalGraph.ancestorSignal Nk p a) graphMesh

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- The native qualification failures of an ancestor `a` relative to a row reference `src`. -/
def qualBad (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (a : Fin p.C) (level : ℕ) (src : Set Ev) (rowa : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (graphMesh : ℝ) (M Tq : ℕ) (qmesh : ℝ) (qbound : ℤ) (qerror qduration : ℝ) : Set Ev :=
  {w | ¬NativeGridQualified (p.childClockReference a level src)
    (p.childClockLabel a level (p.γ a))
    (rowa ∘ (ancCode (d.N k) p a graphMesh ∘ p.childClockPoint a)) M Tq qmesh qbound qerror
      qduration ((hp.frozenPacket a).timeChange w)}

/-- **The post-state stages of one sample.** -/
theorem post_state_assembly {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop meshF envF θF} {rF frF : ℝ} (Rp : BroadResidual F rF frF)
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (c : ℕ) (hib : i + c ≤ m - 1)
    -- the per-sample scalars
    {K θ ε pv aA q d₁ h' a' : ℝ} (hK : 0 < K) (haA : 0 < aA) (hq : 0 < q)
    -- the root survivors
    (E1 : Fin (d.W k) → Set Ev) (hE1res : ∀ w, E1 w ⊆ Rp.residual w)
    (hE1end : ∀ a, F.active a → ∀ z ∈ E1 (p.γ a) ∩ p.F a,
      z ∉ p.oldEndpoints a ∧ z ∉ p.levelEndpoints (i + c))
    (row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ) (graphMesh : ℝ) {Brow : ℝ} (hBK : Brow ≤ K)
    (hfit : ∀ a, F.active a → ∀ x ∈ E1 (p.γ a) ∩ p.F a,
      |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
        ∑ j : Fin 3, row a (ancCode (d.N k) p a graphMesh x) j *
          (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ θ)
    (hcaps : ∀ b, p.lev b = i + c → F.active (p.par^[c] b) → ∀ Se : Set Ev, MeasurableSet Se →
      Se ⊆ E1 (p.γ b) ∩ p.F b →
      CapClauses K ε d₁ h' a'
        (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
        (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
        (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
          O204.Split.δ (d.N k) (p.r (p.lev b))) Se)
    -- the states of all children
    (E2 : Fin (d.W k) → Set Ev) (hE2 : ∀ w, MeasurableSet (E2 w) ∧ E2 w ⊆ E1 w)
    (state : (b : Fin p.C) → b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} →
      Ev → ℕ)
    (value : (b : Fin p.C) → b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} →
      ℕ → Fin 3 → ℝ)
    (palette : (b : Fin p.C) → b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} →
      Measure (Fin 2 → ℤ))
    (hstates : ∀ b (hb : b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)}),
      StateClauses K ε pv (d.ν k (p.γ b)) (unshearedPacketBase p b)
          (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R (p.par^[c] b)) /
            δ (d.N k) (p.r (p.lev b)))
          (E2 (p.γ b) ∩ p.F b) (state b hb) (palette b hb) ∧
        (∀ z, value b hb (state b hb z) =
          (aA / q) • row (p.par^[c] b) (ancCode (d.N k) p (p.par^[c] b) graphMesh z)) ∧
        (∀ j c', |value b hb j c'| ≤ (aA / q) * Brow) ∧
        ∀ x y, state b hb x = state b hb y →
          ancCode (d.N k) p (p.par^[c] b) graphMesh x =
            ancCode (d.N k) p (p.par^[c] b) graphMesh y)
    -- the whole-code regularity cut and its lists
    (U : Fin p.C → Set (Fin 4 → ℤ)) (Pfac chargeR : ENNReal) (hPfac : Pfac ≠ ⊤)
    (hPfac0 : Pfac ≠ 0) (hchargeR : chargeR ≠ ⊤)
    (hregmass : ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume) (E2 (p.γ a) ∩ p.F a) ≤
      Pfac * ((d.ν k (p.γ a)).prod volume)
        ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a) +
        chargeR * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    (hlists : ∀ b, p.lev b = i + c → F.active (p.par^[c] b) → ∀ c' : Fin 3 → ℝ,
      ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧
        ∀ x ∈ ((E2 (p.γ (p.par^[c] b)) ∩ p.F (p.par^[c] b)) ∩
            ancCode (d.N k) p (p.par^[c] b) graphMesh ⁻¹' U (p.par^[c] b)) ∩ p.F b,
          (∀ j : Fin 3, |unshearedPacketBase p b x j - c' j| ≤ θ) →
          (fun j : Fin 3 => ⌊(aA / q) * row (p.par^[c] b)
            (ancCode (d.N k) p (p.par^[c] b) graphMesh x) j / ((aA / q) * θ)⌋) ∈ Fc)
    -- the native qualification relative to the regularity reference
    (M Tq : ℕ) (qmesh qerror qduration : ℝ) (qbound : ℤ)
    (hqmesh : 0 ≤ qmesh) (hqbound : 0 ≤ qbound)
    (hcoeff : Parent.QualificationClock.coefficientCost M * (qmesh * qbound) ≤ K)
    (herror : qerror ≤ θ)
    (hduration : ∀ b, p.lev b = i + c → 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹)))
    (hbadMeas : ∀ a, F.active a → MeasurableSet (qualBad hp a (i + c)
      ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a) (row a) graphMesh M Tq qmesh
        qbound qerror qduration))
    (η : ENNReal) (hη : η ≠ ⊤)
    (hfail : ∀ a, F.active a → ((d.ν k (p.γ a)).prod volume)
      (((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a) ∩
        qualBad hp a (i + c) ((E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a)
          (row a) graphMesh M Tq qmesh qbound qerror qduration) ≤
      η * (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)))
    -- the final numerics
    (hfinal : Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E2 w)) :
    ∃ (density : ℝ) (E : Fin (d.W k) → Set Ev), 0 < density ∧
      (∀ w, E w ⊆ Rp.residual w) ∧
      ENNReal.ofReal density + ENNReal.ofReal density ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w) ∧
      ∀ b : Fin p.C, p.lev b = i + c → F.active (p.par^[c] b) → d.ν k (p.γ b) (p.A b) ≠ 0 →
        ENNReal.ofReal density *
            (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
          ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) →
        ∃ (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
          Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) /
              ENNReal.ofReal K ≤ (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
          CapClauses K ε d₁ h' a'
            (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se ∧
          StateClauses K ε pv (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se st pal ∧
          RowClauses K θ aA q (p.R (p.par^[c] b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) Se Er st G ∧
          QualClauses M K θ aA q (p.j b) ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (d.ν k (p.γ b))
            Se Er bad st G := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcodeMeas (a : Fin p.C) : Measurable (ancCode (d.N k) p a graphMesh) :=
    measurable_clockParentCode p a _ graphMesh
  have hUmeas (a : Fin p.C) : MeasurableSet (ancCode (d.N k) p a graphMesh ⁻¹' U a) :=
    hcodeMeas a (Set.to_countable (U a)).measurableSet
  have hE2base (w : Fin (d.W k)) : E2 w ⊆ Q.base w := fun z hz =>
    broadResidual_subset_base Rp w (hE1res w ((hE2 w).2 hz))
  have hcoverA : ∀ w, ∀ z ∈ E2 w, ∃ a ∈ {a : Fin p.C | F.active a}, p.γ a = w ∧ z ∈ p.F a := by
    intro w z hz
    obtain ⟨a, -, hγ, hzF, hact, -⟩ := Rp.witness w z (hE1res w ((hE2 w).2 hz))
    exact ⟨a, hact, hγ, hzF⟩
  -- 1. the whole-code regularity cut at the ancestor level
  obtain ⟨E3, hE3, hmass3, hslice3⟩ := assemble_same_level_whole_cuts_charge Q hd hp
    {a : Fin p.C | F.active a} i (fun a ha => F.level a ha) E2 (fun w => (hE2 w).1) hE2base
    hcoverA (fun a => ancCode (d.N k) p a graphMesh ⁻¹' U a) (fun a _ => hUmeas a) Pfac chargeR
    (fun a ha => hregmass a ha)
  -- 2. the failure family and the whole bad-child pruning at the child level
  let Eref : Fin p.C → Set Ev := fun a =>
    (E2 (p.γ a) ∩ p.F a) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a
  have hErefMeas (a : Fin p.C) : MeasurableSet (Eref a) :=
    (((hE2 _).1.inter (hF a)).inter (hUmeas a))
  let badFam : Fin (d.W k) → Set Ev := fun w => {z | ∃ a, F.active a ∧ p.γ a = w ∧
    z ∈ Eref a ∩ qualBad hp a (i + c) (Eref a) (row a) graphMesh M Tq qmesh qbound qerror
      qduration}
  have hbadFamMeas (w : Fin (d.W k)) : MeasurableSet (badFam w) := by
    have heq : badFam w = ⋃ a ∈ {a : Fin p.C | F.active a ∧ p.γ a = w},
        Eref a ∩ qualBad hp a (i + c) (Eref a) (row a) graphMesh M Tq qmesh qbound qerror
          qduration := by
      ext z
      simp only [badFam, mem_ofPred_eq, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨a, ha, hw, hz⟩; exact ⟨a, ⟨ha, hw⟩, hz⟩
      · rintro ⟨a, ⟨ha, hw⟩, hz⟩; exact ⟨a, ha, hw, hz⟩
    rw [heq]
    exact MeasurableSet.biUnion (Set.to_countable _)
      (fun a ha => (hErefMeas a).inter (hbadMeas a ha.1))
  obtain ⟨E5, hE5, hloss5, -, hslices5⟩ := discard_failure_heavy_children Q hp
    {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} (i + c)
    (fun b hb => hb.1) E3 badFam (fun w => (hE3 w).1) hbadFamMeas
    (fun w => (hE3 w).2.trans (hE2base w)) (1 / 10000 : ENNReal) (by norm_num) (by norm_num)
  -- 3. the masses
  let M' : (Fin (d.W k) → Set Ev) → ENNReal := fun E' =>
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E' w)
  have hbadMass : M' (fun w => E3 w ∩ badFam w) ≤ η := by
    have htot := weighted_selected_charge_le hd hp {a : Fin p.C | F.active a} i
      (fun a ha => F.level a ha)
      (fun a => ((d.ν k (p.γ a)).prod volume) (Eref a ∩ qualBad hp a (i + c) (Eref a) (row a)
        graphMesh M Tq qmesh qbound qerror qduration)) η (fun a ha => hfail a ha)
    refine le_trans (Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl ?_) htot
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2.2])]
    refine (measure_mono (inter_subset_right.trans ?_)).trans (measure_biUnion_finset_le _ _)
    rintro z ⟨a, ha, hw, hz⟩
    refine mem_biUnion (x := a) ?_ ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
      exact ⟨ha, hw⟩
    · subst hw
      exact hz
  have hloss5' : M' (fun w => E3 w \ E5 w) ≤ 10000 * η := by
    refine hloss5.trans ?_
    have hinv : (1 / 10000 : ENNReal)⁻¹ = 10000 := by
      rw [one_div, inv_inv]
    rw [hinv]
    exact mul_le_mul' le_rfl hbadMass
  have hsplit : M' E3 ≤ M' E5 + M' (fun w => E3 w \ E5 w) := by
    simp only [M', ← Finset.sum_add_distrib, ← mul_add]
    refine Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl ?_
    refine (measure_mono (fun z hz => ?_)).trans (measure_union_le (E5 w) (E3 w \ E5 w))
    by_cases h5 : z ∈ E5 w
    · exact Or.inl h5
    · exact Or.inr ⟨hz, h5⟩
  have hX3 : ENNReal.ofReal (2 / K) + 10000 * η ≤ M' E3 :=
    (ENNReal.mul_le_mul_iff_right hPfac0 hPfac).mp
      ((ENNReal.add_le_add_iff_right hchargeR).mp (hfinal.trans hmass3))
  have h10η : (10000 : ENNReal) * η ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hη
  have hE5mass : ENNReal.ofReal (2 / K) ≤ M' E5 :=
    (ENNReal.add_le_add_iff_right h10η).mp
      (hX3.trans (hsplit.trans (add_le_add le_rfl hloss5')))
  -- 4. the density and the child clauses
  refine ⟨1 / K, E5, by positivity, fun w => ((hE5 w).2.trans ((hE3 w).2.trans
    ((hE2 w).2.trans (hE1res w)))), ?_, ?_⟩
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have h2 : 1 / K + 1 / K = 2 / K := by ring
    rw [h2]
    exact hE5mass
  intro b hlev hact hA hdense
  have hb : b ∈ {b : Fin p.C | p.lev b = i + c ∧ F.active (p.par^[c] b)} := ⟨hlev, hact⟩
  set a := p.par^[c] b with ha
  obtain ⟨hlevA, hγA, hFA⟩ := Broad.iterate_par_spec hp.toOriginal c b
    (show c ≤ p.lev b by omega)
  change p.lev a = p.lev b - c at hlevA
  change p.γ a = p.γ b at hγA
  change p.F b ⊆ p.F a at hFA
  have hlevA' : p.lev a = i := by omega
  -- the child slice is exact and carries a small failure
  have hpos : ((d.ν k (p.γ b)).prod volume) (E5 (p.γ b) ∩ p.F b) ≠ 0 := by
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ hdense
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (mul_ne_zero hA (ENNReal.ofReal_pos.mpr (by positivity)).ne')
  obtain ⟨hexact, hratio⟩ := hslices5 b hb hpos
  have hSe : E5 (p.γ b) ∩ p.F b = Eref a ∩ p.F b := by
    rw [hexact]
    have h3 := hslice3 a hact
    ext z
    constructor
    · rintro ⟨hz3, hzb⟩
      have hza : z ∈ E3 (p.γ a) ∩ p.F a := ⟨by rw [hγA]; exact hz3, hFA hzb⟩
      rw [h3] at hza
      exact ⟨hza, hzb⟩
    · rintro ⟨hza, hzb⟩
      have hza' : z ∈ E3 (p.γ a) ∩ p.F a := by rw [h3]; exact hza
      exact ⟨by rw [← hγA]; exact hza'.1, hzb⟩
  have hSe2 : E5 (p.γ b) ∩ p.F b =
      (E2 (p.γ b) ∩ p.F b) ∩ ancCode (d.N k) p a graphMesh ⁻¹' U a := by
    rw [hSe]
    ext z
    simp only [Eref, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨⟨hz2, -⟩, hzU⟩, hzb⟩
      exact ⟨⟨by rw [← hγA]; exact hz2, hzb⟩, hzU⟩
    · rintro ⟨⟨hz2, hzb⟩, hzU⟩
      exact ⟨⟨⟨by rw [hγA]; exact hz2, hFA hzb⟩, hzU⟩, hzb⟩
  have hSeMeas : MeasurableSet (E5 (p.γ b) ∩ p.F b) := (hE5 _).1.inter (hF b)
  have hSeE1 : E5 (p.γ b) ∩ p.F b ⊆ E1 (p.γ b) ∩ p.F b := fun z hz =>
    ⟨(hE2 _).2 ((hE3 _).2 ((hE5 _).2 hz.1)), hz.2⟩
  have hSeE1a : E5 (p.γ b) ∩ p.F b ⊆ E1 (p.γ a) ∩ p.F a := fun z hz =>
    ⟨by rw [hγA]; exact (hSeE1 hz).1, hFA hz.2⟩
  obtain ⟨hstate, hread, hvbound, hfaith⟩ := hstates b hb
  have hscale0 : 0 ≤ aA / q := (div_pos haA hq).le
  refine ⟨E5 (p.γ b) ∩ p.F b, Eref a ∩ p.F b,
    qualBad hp a (i + c) (Eref a) (row a) graphMesh M Tq qmesh qbound qerror qduration,
    state b hb, value b hb, palette b hb, subset_rfl, hSe.le, ?_, ?_, ?_, ?_, ?_⟩
  · -- the final mass
    rw [Measure.restrict_apply_univ]
    refine le_trans (le_of_eq ?_) hdense
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hK, one_div]
    ring
  · -- caps
    exact hcaps b hlev hact _ hSeMeas hSeE1
  · -- states on whole codes
    rw [hSe2]
    exact hstate.restrict_coarser_code (ancCode (d.N k) p a graphMesh) hfaith (U a)
  · -- rows
    refine rowClauses_of_readout (ancCode (d.N k) p a graphMesh) (row a) haA hq ?_ hread
      (fun x hx => hfit a hact x (hSeE1a hx)) (hlists b hlev hact)
    intro j c'
    refine (hvbound j c').trans ?_
    rw [mul_comm K]
    exact mul_le_mul_of_nonneg_left hBK hscale0
  · -- qualification with the pruned failure
    have hErefF : Eref a ⊆ p.F a := fun z hz => hz.1.2
    have hterminal : ∀ z ∈ Eref a, ∃ terminal : Fin p.C,
        p.lev terminal = m - 1 ∧ p.γ terminal = p.γ a ∧ z ∈ p.F terminal := by
      intro z hz
      have hzH := Rp.subset_H _ (hE1res _ ((hE2 _).2 hz.1.1))
      exact hH _ hzH
    have hSref : E5 (p.γ b) ∩ p.F b ⊆ p.childReference a (i + c) (Eref a) := by
      intro z hz
      have hend := hE1end a hact z (hSeE1a hz)
      exact ⟨⟨(hSe.le hz).1, hend.1⟩, hend.2⟩
    have hG : Measurable (row a ∘ ancCode (d.N k) p a graphMesh) :=
      (measurable_of_countable _).comp (hcodeMeas a)
    have hfailure : (((d.ν k (p.γ b)).prod volume).restrict (E5 (p.γ b) ∩ p.F b))
        (qualBad hp a (i + c) (Eref a) (row a) graphMesh M Tq qmesh qbound qerror qduration) ≤
        (1 / 10000 : ENNReal) *
          (((d.ν k (p.γ b)).prod volume).restrict (E5 (p.γ b) ∩ p.F b)) univ := by
      rw [Measure.restrict_apply (hbadMeas a hact), Measure.restrict_apply_univ]
      refine le_trans (measure_mono ?_) hratio
      intro z hz
      refine ⟨hz.2, a, hact, hγA, ⟨(hSe.le hz.2).1, hz.1⟩⟩
    exact child_qual_clauses_of_original_native_failure_ratio hp a (i + c) (by omega) hib
      (Eref a) hErefF hterminal (hErefMeas a) (E5 (p.γ b) ∩ p.F b) hSref
      (ancCode (d.N k) p a graphMesh) (row a) hG b hlev hγA.symm (fun z hz => hz.2)
      (state b hb) (value b hb) M Tq qmesh qerror qduration aA q K θ qbound
      (fun z _ => by rw [hread z]; rfl) hqmesh hqbound hscale0 hcoeff herror
      (hduration b hlev) (d.ν k (p.γ b)) hfailure

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
