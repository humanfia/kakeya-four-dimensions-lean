-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupEntries.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0581, commit8b919f04,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupEntries.lean (namespace renamed); the component-AC generalization is new here.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupStep

/-!
# One group, indexed by its entries

`group_step_entries` restates `group_step` for a finite set `act` of entries of an arbitrary type:
the entries are indexed by `Fin act.card`, and the lists, representatives and bin data are carried
back to entries. The loss `λ R^{-ε}` of the group recovery is chosen with
`λ = (Σ mass) + #act · H · R^{-ε}`, which bounds the loss by
`R^{-ε} · (Σ mass) + R^{-2ε} · Σ_{act} H`.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The success loss of one group. -/
theorem group_loss_le {R ε H : ℝ} (hR : 0 < R) (hH : 0 < H) (S : ENNReal) (hS : S ≠ ⊤) (k : ℕ) :
    ENNReal.ofReal ((S.toReal + k * H * R ^ (-ε)) * R ^ (-ε)) ≤
      ENNReal.ofReal (R ^ (-ε)) * S + ENNReal.ofReal (R ^ (-(2 * ε))) * (k * ENNReal.ofReal H) := by
  have hRe : 0 < R ^ (-ε) := Real.rpow_pos_of_pos hR _
  have h2 : R ^ (-ε) * R ^ (-ε) = R ^ (-(2 * ε)) := by
    rw [← Real.rpow_add hR]; ring_nf
  have he : (S.toReal + k * H * R ^ (-ε)) * R ^ (-ε) =
      R ^ (-ε) * S.toReal + R ^ (-(2 * ε)) * (k * H) := by
    rw [← h2]; ring
  rw [he, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hRe.le,
    ENNReal.ofReal_toReal hS, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast]

/-- One group of entries: lists, representatives and root tests, indexed by entries. -/
theorem group_step_entries_of_ac {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {R M ε : ℝ} (hR : params.radius ≤ R) (hM : 0 < M) (hε : 0 < ε) (hεp : ε ≤ params.epsilon)
    {Ent : Type*} [DecidableEq Ent] (act : Finset Ent)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (ωw Bw δL : ℝ)
    (hBw : 0 < Bw) (hδL : 0 < δL)
    (cov : Ent → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hcovm : ∀ e ∈ act, MeasurableSet (cov e))
    (hfin : ∀ e ∈ act, (ν.prod volume) (cov e) ≠ ⊤)
    (hACcov : ∀ e ∈ act, ((ν.prod volume).restrict (cov e)).map (obs Bw δL) ≪
      (volume.prod Measure.count))
    (obase : EuclideanSpace ℝ (Fin 3) × ℤ → Real3) (hobase : Measurable obase)
    (lbase : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (hbase : ∀ p : (ℕ × (Fin 6 → ℝ)) × ℝ, obase (obs Bw δL p) = lbase p.1 p.2)
    (F : Ent → RealSheet 2) (F₀ : RealSheet 2)
    (Ptest : Ent → MvPolynomial (Fin 4) ℝ) (s : Ent → ℝ) (pos : Ent → Bool)
    (hP : ∀ e ∈ act, (Ptest e).totalDegree ≤ 2) (hs : ∀ e ∈ act, 0 < s e)
    (hroots : ∀ e ∈ act, ∀ l t, ‖lbase l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F e).f (emb (lbase l t))).re / Bw
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Ptest e) = 0 ∧
      if pos e then
        19 / 20 * s e ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ≤ 21 / 20 * s e
      else
        19 / 20 * s e ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ≤ 21 / 20 * s e)
    (ta tb ηfine ηold : ℝ) (hηfine : 0 < ηfine) (hηold : 0 < ηold)
    (hfitT : ∀ e ∈ act, ∀ p ∈ cov e, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖lbase p.1 t‖ ≤ (1 : ℝ) / 2 ∧ |Bw * gx p.1 t 3 - ((F e).f (emb (lbase p.1 t))).re| ≤ ηfine)
    (hfitP : ∀ e ∈ act, ∀ p ∈ cov e, ‖lbase p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |Bw * gx p.1 p.2 3 - ((F e).f (emb (lbase p.1 p.2))).re| ≤ ηfine ∧
      |Bw * gx p.1 p.2 3 - (F₀.f (emb (lbase p.1 p.2))).re| ≤ ηold)
    (θ H m : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hH : 0 < H)
    (hcount : (act.card : ℝ) ≤ R ^ (d₀ + ε))
    (hcap : ∀ e ∈ act, (ENNReal.ofReal ωw • (ν.prod volume).restrict (cov e)).map
      (obase ∘ obs Bw δL) ≤ ENNReal.ofReal H • volume)
    (hfloor : ∀ e ∈ act, ENNReal.ofReal m ≤ ENNReal.ofReal ωw * (ν.prod volume) (cov e))
    (hθmass : ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m / H))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * R ^ ε)
    (hwidth : 2 * ηfine + δL ≤ M * R ^ (-1 + ε)) :
    ∃ (Lg : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset Ent) (rep : Ent → Ent)
      (Qt : Ent → MvPolynomial (Fin 4) ℝ) (sq m₀ : Ent → ℝ),
      (∀ e', MeasurableSet {o | e' ∈ Lg o}) ∧
      (∀ o, (Lg o).card ≤ 7 ^ Fintype.card (GroupJetIndex params)) ∧
      (∀ e ∈ act, rep e ∈ act ∧ rep (rep e) = rep e ∧
        Qt (rep e) = Qt e ∧ sq (rep e) = sq e ∧ m₀ (rep e) = m₀ e) ∧
      (∀ e ∈ act, (Qt e = Ptest (rep e) ∨ Qt e = pderiv 3 (Ptest (rep e))) ∧
        (sq e = s (rep e) ∨ sq e = |qc (Ptest (rep e))|)) ∧
      (∀ e ∈ act, (Qt e).totalDegree ≤ 2 ∧ 0 < sq e ∧ 0 ≤ m₀ e ∧
        m₀ e ≤ 85 * sq e * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw) ∧
        |qc (Qt e)| * m₀ e ≤ sq e ^ 2 / 40 ∧
        s (rep e) / (1 + 80 * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw)) ≤
          sq e) ∧
      (∀ e ∈ act, ∀ p ∈ cov e, p.1 ∈ rootTestSet (Qt e) (sq e) (m₀ e) ta tb) ∧
      (∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e)) ≤
        (∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e ∩ {p | rep e ∈ Lg (obs Bw δL p)})) +
          (ENNReal.ofReal (R ^ (-ε)) * ∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e) +
            ENNReal.ofReal (R ^ (-(2 * ε))) * (act.card * ENNReal.ofReal H)) := by
  classical
  rcases Nat.eq_zero_or_pos act.card with h0 | hn
  · -- no active entry
    have hact : act = ∅ := Finset.card_eq_zero.mp h0
    refine ⟨fun _ => ∅, id, fun _ => 0, fun _ => 1, fun _ => 0, fun _ => MeasurableSet.const _,
      fun _ => by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hact]
  set n := act.card with hndef
  have hRpos : 0 < R := by linarith [params.radius_two]
  -- indexing the active entries
  let ent : Fin n → Ent := fun a => (act.equivFin.symm a : Ent)
  have hent_mem : ∀ a, ent a ∈ act := fun a => (act.equivFin.symm a).2
  let idx : Ent → Fin n := fun e => if he : e ∈ act then act.equivFin ⟨e, he⟩ else ⟨0, hn⟩
  have hent_idx : ∀ e ∈ act, ent (idx e) = e := by
    intro e he
    simp only [ent, idx, dif_pos he, Equiv.symm_apply_apply]
  have hidx_ent : ∀ a, idx (ent a) = a := by
    intro a
    simp only [idx, dif_pos (hent_mem a), ent, Subtype.coe_eta, Equiv.apply_symm_apply]
  have hent_inj : Function.Injective ent := by
    intro a b hab
    rw [← hidx_ent a, ← hidx_ent b, hab]
  have hsum : ∀ f : Ent → ENNReal, (∑ a : Fin n, f (ent a)) = ∑ e ∈ act, f e := by
    intro f
    rw [← Finset.sum_coe_sort act f]
    exact Equiv.sum_comp act.equivFin.symm (fun x : act => f x)
  -- the mass and the loss
  set S : ENNReal := ∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e) with hSdef
  have hSfin : S ≠ ⊤ := by
    rw [hSdef]
    refine ENNReal.sum_ne_top.mpr fun e he => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin e he)
  set lam : ℝ := S.toReal + n * H * R ^ (-ε) with hlamdef
  have hRe : 0 < R ^ (-ε) := Real.rpow_pos_of_pos hRpos _
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlam : 0 < lam := by
    have : 0 < (n : ℝ) * H * R ^ (-ε) := by positivity
    have := ENNReal.toReal_nonneg (a := S)
    linarith
  have htot : (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov (ent a))) ≤ ENNReal.ofReal lam := by
    rw [hsum (fun e => ENNReal.ofReal ωw * (ν.prod volume) (cov e)), ← hSdef,
      ← ENNReal.ofReal_toReal hSfin]
    have h0 : 0 ≤ (n : ℝ) * H * R ^ (-ε) := by positivity
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hbudget : (n : ℝ) * H ≤ lam * R ^ ε := by
    have h1 : R ^ (-ε) * R ^ ε = 1 := by
      rw [← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero]
    have h2 : (n : ℝ) * H = n * H * R ^ (-ε) * R ^ ε := by
      rw [mul_assoc ((n : ℝ) * H), h1, mul_one]
    rw [h2]
    have := ENNReal.toReal_nonneg (a := S)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hRpos.le _)
  -- the group step on the indexed entries
  obtain ⟨Lg, rep, Qt, sq, m₀, hLm, hLc, hrep, hQrep, hchoice, hbnd, hmem, hsucc⟩ :=
    group_step_of_ac hGR hR hM hε hεp hn ν ωw Bw δL hBw hδL (fun a => cov (ent a))
      (fun a => hcovm _ (hent_mem a)) (fun a => hfin _ (hent_mem a)) (fun a => hACcov _ (hent_mem a))
      obase hobase lbase hbase (fun a => F (ent a)) F₀ (fun a => Ptest (ent a)) (fun a => s (ent a))
      (fun a => pos (ent a)) (fun a => hP _ (hent_mem a)) (fun a => hs _ (hent_mem a))
      (fun a => hroots _ (hent_mem a)) ta tb ηfine ηold hηfine hηold
      (fun a => hfitT _ (hent_mem a)) (fun a => hfitP _ (hent_mem a)) θ H m lam hθ hθ1 hH hlam
      hcount htot hbudget (fun a => hcap _ (hent_mem a)) (fun a => hfloor _ (hent_mem a))
      hθmass hremez hwidth
  refine ⟨fun o => (Lg o).image ent, fun e => if e ∈ act then ent (rep (idx e)) else e,
    fun e => Qt (idx e), fun e => sq (idx e), fun e => m₀ (idx e), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e'
    have h : {o | e' ∈ (Lg o).image ent} =
        ⋃ a ∈ Finset.univ.filter (fun a => ent a = e'), {o | a ∈ Lg o} := by
      ext o
      simp only [Finset.mem_image, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, hae⟩; exact ⟨a, hae, ha⟩
      · rintro ⟨a, hae, ha⟩; exact ⟨a, ha, hae⟩
    rw [h]
    exact Finset.measurableSet_biUnion _ fun a _ => hLm a
  · intro o
    exact Finset.card_image_le.trans (hLc o)
  · intro e he
    have hr1 : ent (rep (idx e)) ∈ act := hent_mem _
    simp only [if_pos he, if_pos hr1, hidx_ent, hrep]
    exact ⟨hr1, trivial, (hQrep _).1, (hQrep _).2.1, (hQrep _).2.2⟩
  · intro e he
    simp only [if_pos he, hidx_ent]
    exact hchoice (idx e)
  · intro e he
    simp only [if_pos he, hidx_ent]
    exact hbnd (idx e)
  · intro e he p hp
    rw [← hent_idx e he] at hp
    exact hmem (idx e) p hp
  · -- success
    have hset : ∀ a, {p : (ℕ × (Fin 6 → ℝ)) × ℝ | rep a ∈ Lg (obs Bw δL p)} =
        {p | (if ent a ∈ act then ent (rep (idx (ent a))) else ent a) ∈
          (Lg (obs Bw δL p)).image ent} := by
      intro a
      ext p
      simp only [Set.mem_ofPred_eq, if_pos (hent_mem a), hidx_ent]
      exact hent_inj.mem_finset_image.symm
    have hloss := group_loss_le (ε := ε) hRpos hH S hSfin n
    calc (∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e))
        = ∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov (ent a)) :=
          (hsum (fun e => ENNReal.ofReal ωw * (ν.prod volume) (cov e))).symm
      _ ≤ (∑ a, ENNReal.ofReal ωw * (ν.prod volume)
            (cov (ent a) ∩ {p | rep a ∈ Lg (obs Bw δL p)})) + ENNReal.ofReal (lam * R ^ (-ε)) :=
          hsucc
      _ ≤ _ := by
        refine add_le_add (le_of_eq ?_) ?_
        · rw [← hsum (fun e => ENNReal.ofReal ωw * (ν.prod volume) (cov e ∩
            {p | (if e ∈ act then ent (rep (idx e)) else e) ∈ (Lg (obs Bw δL p)).image ent}))]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hset a]
        · rw [hSdef] at hloss ⊢
          simpa only [hlamdef] using hloss

/-- Full-world density-law version of the component-AC entry step. -/
theorem group_step_entries {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {R M ε : ℝ} (hR : params.radius ≤ R) (hM : 0 < M) (hε : 0 < ε) (hεp : ε ≤ params.epsilon)
    {Ent : Type*} [DecidableEq Ent] (act : Finset Ent)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (Ew : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ωw Bw δL : ℝ)
    (hBw : 0 < Bw) (hδL : 0 < δL) (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (hlaw : ((ν.prod volume).restrict Ew).map (obs Bw δL) =
      (volume.prod Measure.count).withDensity g)
    (cov : Ent → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hcovm : ∀ e ∈ act, MeasurableSet (cov e))
    (hcovE : ∀ e ∈ act, cov e ⊆ Ew) (hfin : ∀ e ∈ act, (ν.prod volume) (cov e) ≠ ⊤)
    (obase : EuclideanSpace ℝ (Fin 3) × ℤ → Real3) (hobase : Measurable obase)
    (lbase : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (hbase : ∀ p : (ℕ × (Fin 6 → ℝ)) × ℝ, obase (obs Bw δL p) = lbase p.1 p.2)
    (F : Ent → RealSheet 2) (F₀ : RealSheet 2)
    (Ptest : Ent → MvPolynomial (Fin 4) ℝ) (s : Ent → ℝ) (pos : Ent → Bool)
    (hP : ∀ e ∈ act, (Ptest e).totalDegree ≤ 2) (hs : ∀ e ∈ act, 0 < s e)
    (hroots : ∀ e ∈ act, ∀ l t, ‖lbase l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F e).f (emb (lbase l t))).re / Bw
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Ptest e) = 0 ∧
      if pos e then
        19 / 20 * s e ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ≤ 21 / 20 * s e
      else
        19 / 20 * s e ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest e)) ≤ 21 / 20 * s e)
    (ta tb ηfine ηold : ℝ) (hηfine : 0 < ηfine) (hηold : 0 < ηold)
    (hfitT : ∀ e ∈ act, ∀ p ∈ cov e, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖lbase p.1 t‖ ≤ (1 : ℝ) / 2 ∧ |Bw * gx p.1 t 3 - ((F e).f (emb (lbase p.1 t))).re| ≤ ηfine)
    (hfitP : ∀ e ∈ act, ∀ p ∈ cov e, ‖lbase p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |Bw * gx p.1 p.2 3 - ((F e).f (emb (lbase p.1 p.2))).re| ≤ ηfine ∧
      |Bw * gx p.1 p.2 3 - (F₀.f (emb (lbase p.1 p.2))).re| ≤ ηold)
    (θ H m : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hH : 0 < H)
    (hcount : (act.card : ℝ) ≤ R ^ (d₀ + ε))
    (hcap : ∀ e ∈ act, (ENNReal.ofReal ωw • (ν.prod volume).restrict (cov e)).map
      (obase ∘ obs Bw δL) ≤ ENNReal.ofReal H • volume)
    (hfloor : ∀ e ∈ act, ENNReal.ofReal m ≤ ENNReal.ofReal ωw * (ν.prod volume) (cov e))
    (hθmass : ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m / H))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * R ^ ε)
    (hwidth : 2 * ηfine + δL ≤ M * R ^ (-1 + ε)) :
    ∃ (Lg : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset Ent) (rep : Ent → Ent)
      (Qt : Ent → MvPolynomial (Fin 4) ℝ) (sq m₀ : Ent → ℝ),
      (∀ e', MeasurableSet {o | e' ∈ Lg o}) ∧
      (∀ o, (Lg o).card ≤ 7 ^ Fintype.card (GroupJetIndex params)) ∧
      (∀ e ∈ act, rep e ∈ act ∧ rep (rep e) = rep e ∧
        Qt (rep e) = Qt e ∧ sq (rep e) = sq e ∧ m₀ (rep e) = m₀ e) ∧
      (∀ e ∈ act, (Qt e = Ptest (rep e) ∨ Qt e = pderiv 3 (Ptest (rep e))) ∧
        (sq e = s (rep e) ∨ sq e = |qc (Ptest (rep e))|)) ∧
      (∀ e ∈ act, (Qt e).totalDegree ≤ 2 ∧ 0 < sq e ∧ 0 ≤ m₀ e ∧
        m₀ e ≤ 85 * sq e * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw) ∧
        |qc (Qt e)| * m₀ e ≤ sq e ^ 2 / 40 ∧
        s (rep e) / (1 + 80 * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw)) ≤
          sq e) ∧
      (∀ e ∈ act, ∀ p ∈ cov e, p.1 ∈ rootTestSet (Qt e) (sq e) (m₀ e) ta tb) ∧
      (∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e)) ≤
        (∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e ∩ {p | rep e ∈ Lg (obs Bw δL p)})) +
          (ENNReal.ofReal (R ^ (-ε)) * ∑ e ∈ act, ENNReal.ofReal ωw * (ν.prod volume) (cov e) +
            ENNReal.ofReal (R ^ (-(2 * ε))) * (act.card * ENNReal.ofReal H)) := by
  have hO : Measurable (obs Bw δL) := measurable_gobs' Bw δL
  have hACcov : ∀ e ∈ act, ((ν.prod volume).restrict (cov e)).map (obs Bw δL) ≪
      (volume.prod Measure.count) := by
    intro e he
    refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    have h1 : ((volume.prod Measure.count).withDensity g) S = 0 :=
      withDensity_absolutelyContinuous _ _ hS0
    rw [← hlaw, Measure.map_apply hO hS, Measure.restrict_apply (hO hS)] at h1
    rw [Measure.map_apply hO hS, Measure.restrict_apply (hO hS)]
    exact measure_mono_null (Set.inter_subset_inter_right _ (hcovE e he)) h1
  exact group_step_entries_of_ac hGR hR hM hε hεp act ν ωw Bw δL hBw hδL cov hcovm hfin hACcov
    obase hobase lbase hbase F F₀ Ptest s pos hP hs hroots ta tb ηfine ηold hηfine hηold hfitT hfitP
    θ H m hθ hθ1 hH hcount hcap hfloor hθmass hremez hwidth

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
