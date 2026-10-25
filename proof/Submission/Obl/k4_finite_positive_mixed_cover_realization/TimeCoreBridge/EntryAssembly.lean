-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/EntryAssembly.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0581, commit7ceccd3d,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/EntryAssembly.lean (namespace renamed), generalized here to component observation AC.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupEntries

/-!
# The analytic output from entry sheets

`coreOutput_of_entry_sheets` assembles `CoreOutput` at one sample from covered incidences of the
entries, one sheet and one selected root test for every active entry (one whose covered set is
nonempty), one true sheet for every group, group coordinates, caps and floors, and the numerical
conditions of the group recovery. Every group is run through `group_step_entries`; the results
are glued by `coreOutput_of_groups`.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The first time of the sub-block of a group. -/
noncomputable def groupStart {C s₀ K : ℕ} (j : Fin C → ℕ) (Ti : ℕ) (G : Group C s₀ K) : ℝ :=
  (subIdx s₀ (j G.1) G.2.1 : ℝ) / (2 : ℝ) ^ (Ti + s₀)

/-- The last time of the sub-block of a group. -/
noncomputable def groupEnd {C s₀ K : ℕ} (j : Fin C → ℕ) (Ti : ℕ) (G : Group C s₀ K) : ℝ :=
  ((subIdx s₀ (j G.1) G.2.1 : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)

open Classical in
/-- **CoreOutput from entry sheets.** -/
theorem coreOutput_of_entry_sheets_of_ac {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {Rg M εg : ℝ} (hR : params.radius ≤ Rg) (hM : 0 < M) (hε : 0 < εg)
    (hεp : εg ≤ params.epsilon)
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {r₀ h θo β : ℝ} {Mc : ℕ}
    {C : ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {n : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {Ti s₀ K : ℕ}
    (hB : ∀ w, 0 < B w) (hNk : 1 ≤ Nk) (hδL : 0 < δ Nk L) (hδr : 0 < δ Nk r₀)
    -- covered incidences
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e, cov e ⊆ {p | p ∈ E (γ (old e.1)) ∧
      p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧ p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1})
    (hcovm : ∀ e, MeasurableSet (cov e))
    (hcovdisj : ∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e'))
    (hfin : ∀ e, ((ν (γ (old e.1))).prod volume) (cov e) ≠ ⊤)
    (hACcov : ∀ e, (((ν (γ (old e.1))).prod volume).restrict (cov e)).map
      (obs (B (γ (old e.1))) (δ Nk L)) ≪ (volume.prod Measure.count))
    -- group coordinates
    (ob : Group C s₀ K → EuclideanSpace ℝ (Fin 3) × ℤ → Real3) (hob : ∀ G, Measurable (ob G))
    (lb : Group C s₀ K → (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (hbase : ∀ G (p : (ℕ × (Fin 6 → ℝ)) × ℝ), ob G (obs (B (γ G.1)) (δ Nk L) p) = lb G p.1 p.2)
    -- sheets and selected root tests
    (Fe : Entry n s₀ K → RealSheet 2) (F₀ : Group C s₀ K → RealSheet 2)
    (Pe : Entry n s₀ K → MvPolynomial (Fin 4) ℝ) (se : Entry n s₀ K → ℝ)
    (pe : Entry n s₀ K → Bool)
    (hPe : ∀ e, (cov e).Nonempty → (Pe e).totalDegree ≤ 2 ∧ 0 < se e)
    (hroots : ∀ e, (cov e).Nonempty → ∀ l t, ‖lb (entryGroup old e) l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((Fe e).f (emb (lb (entryGroup old e) l t))).re / B (γ (old e.1))
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Pe e) = 0 ∧
      if pe e then
        19 / 20 * se e ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ≤ 21 / 20 * se e
      else
        19 / 20 * se e ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Pe e)) ≤ 21 / 20 * se e)
    (ηfine ηold : ℝ) (hηfine : 0 < ηfine) (hηold : 0 < ηold)
    (hfitT : ∀ e, ∀ p ∈ cov e, ∀ t, t = groupStart j Ti (entryGroup old e) ∨
      t = (groupStart j Ti (entryGroup old e) + groupEnd j Ti (entryGroup old e)) / 2 ∨
      t = groupEnd j Ti (entryGroup old e) →
      ‖lb (entryGroup old e) p.1 t‖ ≤ (1 : ℝ) / 2 ∧
      |B (γ (old e.1)) * gx p.1 t 3 - ((Fe e).f (emb (lb (entryGroup old e) p.1 t))).re| ≤ ηfine)
    (hfitP : ∀ e, ∀ p ∈ cov e, ‖lb (entryGroup old e) p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |B (γ (old e.1)) * gx p.1 p.2 3 - ((Fe e).f (emb (lb (entryGroup old e) p.1 p.2))).re| ≤
        ηfine ∧
      |B (γ (old e.1)) * gx p.1 p.2 3 -
        ((F₀ (entryGroup old e)).f (emb (lb (entryGroup old e) p.1 p.2))).re| ≤ ηold)
    -- caps, floors and the group recovery numerics
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (H m : Group C s₀ K → ℝ) (hH : ∀ G, 0 < H G)
    (hcount : ∀ G, ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ) ≤
      Rg ^ (d₀ + εg))
    (hcap : ∀ e, (cov e).Nonempty →
      (ENNReal.ofReal (ω (γ (old e.1))) • ((ν (γ (old e.1))).prod volume).restrict (cov e)).map
        (ob (entryGroup old e) ∘ obs (B (γ (old e.1))) (δ Nk L)) ≤
        ENNReal.ofReal (H (entryGroup old e)) • volume)
    (hfloor : ∀ e, (cov e).Nonempty → ENNReal.ofReal (m (entryGroup old e)) ≤
      ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e))
    (hθmass : ∀ G, ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m G / H G))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * Rg ^ εg)
    (hwidth : 2 * ηfine + δ Nk L ≤ M * Rg ^ (-1 + εg))
    -- bounds of the tests and scales, and the output threshold
    (hPcoef : ∀ e, (cov e).Nonempty → ∀ k,
      |(Pe e).coeff k| ≤ Nk ^ Mc ∧ |(pderiv 3 (Pe e)).coeff k| ≤ Nk ^ Mc)
    (hscale : ∀ e, (cov e).Nonempty → se e ≤ Nk ^ Mc ∧ |qc (Pe e)| ≤ Nk ^ Mc ∧
      (1 + 80 * ((ηfine + (∑ i, groupJetWidth params Rg M εg i) / params.lower) /
        B (γ (old e.1)))) / se e ≤ Nk ^ Mc)
    (hthr : 340 * (ηfine + (∑ i, groupJetWidth params Rg M εg i) / params.lower) ≤
      δ Nk r₀ * Nk ^ (-(θo * h * L)))
    -- group observation domains, list sizes and the total
    (S : Group C s₀ K → Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hSm : ∀ G, MeasurableSet (S G))
    (hsupp : ∀ e, ∀ p ∈ cov e, obs (B (γ (old e.1))) (δ Nk L) p ∈ S (entryGroup old e))
    (Dcount : ℕ)
    (hD : ∀ w o, ((Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).card) ≤
      Dcount)
    (hcardE : (Fintype.card (Entry n s₀ K) : ℝ) ≤ Nk ^ Mc)
    (hlistβ : ((7 ^ Fintype.card (GroupJetIndex params) * Dcount : ℕ) : ℝ) ≤ Nk ^ β)
    (htotal : ENNReal.ofReal (Nk ^ (-β)) +
        (ENNReal.ofReal (Rg ^ (-εg)) * ∑ e, ENNReal.ofReal (ω (γ (old e.1))) *
            ((ν (γ (old e.1))).prod volume) (cov e) +
          ENNReal.ofReal (Rg ^ (-(2 * εg))) *
            ∑ e, (if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0)) ≤
      ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) :
    CoreOutput Nk L W ω ν E B r₀ h θo β Mc γ j c u Q R old R' A' Ti s₀ K := by
  classical
  set ηbin := (∑ i, groupJetWidth params Rg M εg i) / params.lower with hηbin
  let act : Group C s₀ K → Finset (Entry n s₀ K) := fun G =>
    Finset.univ.filter (fun e => entryGroup old e = G ∧ (cov e).Nonempty)
  have hact : ∀ G e, e ∈ act G ↔ entryGroup old e = G ∧ (cov e).Nonempty := by
    intro G e
    simp only [act, Finset.mem_filter, Finset.mem_univ, true_and]
  -- every group through the group step
  have hstep := fun G : Group C s₀ K =>
    group_step_entries_of_ac hGR hR hM hε hεp (act G) (ν (γ G.1)) (ω (γ G.1)) (B (γ G.1))
      (δ Nk L) (hB _) hδL cov (fun e _ => hcovm e)
      (fun e he => by obtain ⟨rfl, -⟩ := (hact G e).1 he; exact hfin e)
      (fun e he => by obtain ⟨rfl, -⟩ := (hact G e).1 he; exact hACcov e)
      (ob G) (hob G) (lb G) (hbase G) Fe (F₀ G) Pe se pe
      (fun e he => by obtain ⟨rfl, hne⟩ := (hact G e).1 he; exact (hPe e hne).1)
      (fun e he => by obtain ⟨rfl, hne⟩ := (hact G e).1 he; exact (hPe e hne).2)
      (fun e he => by obtain ⟨rfl, hne⟩ := (hact G e).1 he; exact hroots e hne)
      (groupStart j Ti G) (groupEnd j Ti G) ηfine ηold hηfine hηold
      (fun e he => by obtain ⟨rfl, -⟩ := (hact G e).1 he; exact hfitT e)
      (fun e he => by obtain ⟨rfl, -⟩ := (hact G e).1 he; exact hfitP e)
      θ (H G) (m G) hθ hθ1 (hH G)
      ((Nat.cast_le.mpr (Finset.card_le_card (fun e he => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ((hact G e).1 he).1⟩))).trans (hcount G))
      (fun e he => by obtain ⟨rfl, hne⟩ := (hact G e).1 he; exact hcap e hne)
      (fun e he => by obtain ⟨rfl, hne⟩ := (hact G e).1 he; exact hfloor e hne)
      (hθmass G) hremez hwidth
  choose Lg rep Qt sq m₀ hLm hLc hrepP hchoice hbnd hmem hsucc using hstep
  -- global representatives and bin data
  let repOf : Entry n s₀ K → Entry n s₀ K := fun e =>
    if (cov e).Nonempty then rep (entryGroup old e) e else e
  let Pg : Entry n s₀ K → MvPolynomial (Fin 4) ℝ := fun e =>
    if (cov e).Nonempty then Qt (entryGroup old e) e else 0
  let sg : Entry n s₀ K → ℝ := fun e => if (cov e).Nonempty then sq (entryGroup old e) e else 1
  let mg : Entry n s₀ K → ℝ := fun e => if (cov e).Nonempty then m₀ (entryGroup old e) e else 0
  have hmemact : ∀ e, (cov e).Nonempty → e ∈ act (entryGroup old e) :=
    fun e hne => (hact _ e).2 ⟨rfl, hne⟩
  -- the representative of an active entry is active in the same group
  have hrepAct : ∀ e, (cov e).Nonempty →
      (cov (repOf e)).Nonempty ∧ entryGroup old (repOf e) = entryGroup old e ∧
      repOf e = rep (entryGroup old e) e := by
    intro e hne
    have h1 := (hrepP _ e (hmemact e hne)).1
    obtain ⟨hG, hne'⟩ := (hact _ _).1 h1
    have hre : repOf e = rep (entryGroup old e) e := if_pos hne
    rw [hre]
    exact ⟨hne', hG, rfl⟩
  have hdata : ∀ e, (cov e).Nonempty →
      Pg (repOf e) = Qt (entryGroup old e) e ∧ sg (repOf e) = sq (entryGroup old e) e ∧
        mg (repOf e) = m₀ (entryGroup old e) e := by
    intro e hne
    obtain ⟨hne', hG, hre⟩ := hrepAct e hne
    obtain ⟨-, -, hQ, hs, hm⟩ := hrepP _ e (hmemact e hne)
    rw [hre] at hne' hG ⊢
    have e1 : Pg (rep (entryGroup old e) e) = Qt (entryGroup old e) (rep (entryGroup old e) e) := by
      simp only [Pg, if_pos hne', hG]
    have e2 : sg (rep (entryGroup old e) e) = sq (entryGroup old e) (rep (entryGroup old e) e) := by
      simp only [sg, if_pos hne', hG]
    have e3 : mg (rep (entryGroup old e) e) = m₀ (entryGroup old e) (rep (entryGroup old e) e) := by
      simp only [mg, if_pos hne', hG]
    rw [e1, e2, e3]
    exact ⟨hQ, hs, hm⟩
  have hδpos : ∀ x : ℝ, 0 < Nk ^ x := fun x => Real.rpow_pos_of_pos (by linarith) x
  have hNMc : (1 : ℝ) ≤ Nk ^ Mc := one_le_pow₀ hNk
  have hηbin0 : 0 ≤ ηbin := by
    rw [hηbin]
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) params.lower_pos.le
    exact (mul_pos (params.upper_pos _) (mul_pos hM
      (Real.rpow_pos_of_pos (by linarith [params.radius_two]) _))).le
  refine coreOutput_of_groups cov hcov hcovm hcovdisj repOf Pg sg mg ?_ ?_ ?_ ?_ ?_ ?_ S hSm hsupp
    Dcount (7 ^ Fintype.card (GroupJetIndex params)) hD Lg (fun G => hLm G) (fun G => hLc G)
    (fun G => ENNReal.ofReal (Rg ^ (-εg)) * ∑ e ∈ act G, ENNReal.ofReal (ω (γ G.1)) *
        ((ν (γ G.1)).prod volume) (cov e) +
      ENNReal.ofReal (Rg ^ (-(2 * εg))) * ((act G).card * ENNReal.ofReal (H G))) ?_ hB
    (by linarith) ?_ hcardE (by simpa only [mul_comm] using hlistβ) ?_
  · -- degrees
    intro b
    by_cases hb : (cov b).Nonempty
    · simp only [Pg, if_pos hb]
      exact (hbnd _ b (hmemact b hb)).1
    · simp only [Pg, if_neg hb, totalDegree_zero, zero_le]
  · -- coefficients
    intro b k
    by_cases hb : (cov b).Nonempty
    · simp only [Pg, if_pos hb]
      have hra := hrepAct b hb
      rcases (hchoice _ b (hmemact b hb)).1 with hQ | hQ
      · rw [hQ, ← hra.2.2]; exact (hPcoef _ hra.1 k).1
      · rw [hQ, ← hra.2.2]; exact (hPcoef _ hra.1 k).2
    · have h0 : Pg b = 0 := if_neg hb
      rw [h0]
      simpa using (zero_lt_one.trans_le hNMc).le
  · -- scales
    intro b
    by_cases hb : (cov b).Nonempty
    · simp only [sg, if_pos hb]
      have hra := hrepAct b hb
      obtain ⟨-, hsq, -, -, -, hlow⟩ := hbnd _ b (hmemact b hb)
      have hsc := hscale _ hra.1
      have hγ : old (repOf b).1 = old b.1 := congrArg Prod.fst hra.2.1
      rw [hγ, hra.2.2] at hsc
      refine ⟨hsq, ?_, ?_⟩
      · rcases (hchoice _ b (hmemact b hb)).2 with hs | hs
        · rw [hs]; exact hsc.1
        · rw [hs]; exact hsc.2.1
      · have hse := (hPe _ hra.1).2
        rw [hra.2.2] at hse
        have hden : 0 < 1 + 80 * ((ηfine + ηbin) / B (γ (old b.1))) := by
          have := hB (γ (old b.1)); positivity
        calc (sq (entryGroup old b) b)⁻¹ ≤
              (se (rep (entryGroup old b) b) / (1 + 80 * ((ηfine + ηbin) / B (γ (old b.1)))))⁻¹ :=
            inv_anti₀ (div_pos hse hden) hlow
          _ = (1 + 80 * ((ηfine + ηbin) / B (γ (old b.1)))) / se (rep (entryGroup old b) b) := by
            rw [inv_div]
          _ ≤ Nk ^ Mc := hsc.2.2
    · simp only [sg, if_neg hb]
      exact ⟨one_pos, hNMc, by rw [inv_one]; exact hNMc⟩
  · -- thresholds
    intro e
    by_cases he : (cov e).Nonempty
    · obtain ⟨hP, hs, hm⟩ := hdata e he
      rw [hm, hs]
      obtain ⟨-, hsq, hm0, hm1, -, -⟩ := hbnd _ e (hmemact e he)
      refine ⟨hm0, hm1.trans ?_⟩
      unfold rootThreshold
      have hBw := hB (γ (old e.1))
      have hthr' : 85 * ((ηfine + ηbin) / B (γ (old e.1))) ≤
          δ Nk r₀ * Nk ^ (-(θo * h * L)) / (4 * B (γ (old e.1))) := by
        calc 85 * ((ηfine + ηbin) / B (γ (old e.1)))
            = (340 * (ηfine + ηbin)) / (4 * B (γ (old e.1))) := by field_simp; ring
          _ ≤ _ := div_le_div_of_nonneg_right hthr (by positivity)
      calc 85 * sq (entryGroup old e) e * ((ηfine + ηbin) / B (γ (old e.1)))
          = sq (entryGroup old e) e * (85 * ((ηfine + ηbin) / B (γ (old e.1)))) := by ring
        _ ≤ sq (entryGroup old e) e * (δ Nk r₀ * Nk ^ (-(θo * h * L)) / (4 * B (γ (old e.1)))) :=
          mul_le_mul_of_nonneg_left hthr' hsq.le
        _ = _ := by ring
    · have hre : repOf e = e := by simp only [repOf, if_neg he]
      rw [hre]
      simp only [mg, sg, if_neg he, le_refl, true_and]
      unfold rootThreshold
      have := hB (γ (old e.1))
      have := hδpos (-(θo * h * L))
      positivity
  · -- curvature
    intro b
    by_cases hb : (cov b).Nonempty
    · simp only [Pg, sg, mg, if_pos hb]
      exact (hbnd _ b (hmemact b hb)).2.2.2.2.1
    · simp only [Pg, sg, mg, if_neg hb, mul_zero]
      norm_num
  · -- root tests
    intro e p hp
    have he : (cov e).Nonempty := ⟨p, hp⟩
    obtain ⟨hP, hs, hm⟩ := hdata e he
    rw [hP, hs, hm]
    exact hmem _ e (hmemact e he) p hp
  · -- per-group success
    intro G
    have hsub : act G ⊆ Finset.univ.filter (fun e => entryGroup old e = G) := fun e he =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hact G e).1 he).1⟩
    have hzero : ∀ e ∈ Finset.univ.filter (fun e => entryGroup old e = G), e ∉ act G →
        cov e = ∅ := by
      intro e he hna
      by_contra hne
      exact hna ((hact G e).2 ⟨(Finset.mem_filter.mp he).2, Set.nonempty_iff_ne_empty.mpr hne⟩)
    have hworld : ∀ e ∈ act G, old e.1 = G.1 := fun e he =>
      (congrArg Prod.fst ((hact G e).1 he).1 : _)
    rw [← Finset.sum_subset hsub (fun e he hna => by rw [hzero e he hna, measure_empty, mul_zero]),
      ← Finset.sum_subset hsub (fun e he hna => by
        rw [hzero e he hna, Set.empty_inter, measure_empty, mul_zero])]
    have h1 : (∑ e ∈ act G, ENNReal.ofReal (ω (γ (old e.1))) *
          ((ν (γ (old e.1))).prod volume) (cov e)) =
        ∑ e ∈ act G, ENNReal.ofReal (ω (γ G.1)) * ((ν (γ G.1)).prod volume) (cov e) :=
      Finset.sum_congr rfl fun e he => by rw [hworld e he]
    have h2 : (∑ e ∈ act G, ENNReal.ofReal (ω (γ (old e.1))) *
          ((ν (γ (old e.1))).prod volume)
            (cov e ∩ {p | repOf e ∈ Lg G (obs (B (γ (old e.1))) (δ Nk L) p)})) =
        ∑ e ∈ act G, ENNReal.ofReal (ω (γ G.1)) * ((ν (γ G.1)).prod volume)
          (cov e ∩ {p | rep G e ∈ Lg G (obs (B (γ G.1)) (δ Nk L) p)}) := by
      refine Finset.sum_congr rfl fun e he => ?_
      obtain ⟨hG, hne⟩ := (hact G e).1 he
      have hre : repOf e = rep G e := by simp only [repOf, if_pos hne, hG]
      rw [hre, hworld e he]
    rw [h1, h2]
    exact hsucc G
  · -- finite losses
    intro G
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)⟩
    refine ENNReal.sum_ne_top.mpr fun e he => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hw : old e.1 = G.1 := congrArg Prod.fst ((hact G e).1 he).1
    have := hfin e
    rwa [hw] at this
  · -- the total
    refine le_trans (add_le_add le_rfl (le_of_eq ?_)) htotal
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    · -- masses
      rw [← Finset.sum_fiberwise Finset.univ (entryGroup old)
        (fun e => ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e))]
      refine Finset.sum_congr rfl fun G _ => ?_
      have hsub : act G ⊆ Finset.univ.filter (fun e => entryGroup old e = G) := fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hact G e).1 he).1⟩
      rw [← Finset.sum_subset hsub (fun e he hna => by
        have hce : cov e = ∅ := by
          by_contra hne
          exact hna ((hact G e).2 ⟨(Finset.mem_filter.mp he).2,
            Set.nonempty_iff_ne_empty.mpr hne⟩)
        rw [hce, measure_empty, mul_zero])]
      refine Finset.sum_congr rfl fun e he => ?_
      have hw : old e.1 = G.1 := congrArg Prod.fst ((hact G e).1 he).1
      rw [hw]
    · -- caps
      rw [← Finset.sum_fiberwise Finset.univ (entryGroup old)
        (fun e => if (cov e).Nonempty then ENNReal.ofReal (H (entryGroup old e)) else 0)]
      refine Finset.sum_congr rfl fun G _ => ?_
      have hsub : act G ⊆ Finset.univ.filter (fun e => entryGroup old e = G) := fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hact G e).1 he).1⟩
      rw [← Finset.sum_subset hsub (fun e he hna => by
        have hne : ¬ (cov e).Nonempty := fun hne =>
          hna ((hact G e).2 ⟨(Finset.mem_filter.mp he).2, hne⟩)
        rw [if_neg hne])]
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_congr rfl fun e he => ?_
      obtain ⟨hG, hne⟩ := (hact G e).1 he
      rw [if_pos hne, hG]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
