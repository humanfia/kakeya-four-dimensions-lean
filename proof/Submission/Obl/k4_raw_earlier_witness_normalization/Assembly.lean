import Submission.Obl.k4_raw_earlier_witness_normalization.MeasureNormalize
import Submission.Obl.k4_raw_earlier_witness_normalization.Counting

namespace Submission.Obl.k4_raw_earlier_witness_normalization

open MeasureTheory
open scoped ENNReal BigOperators

/-- The local polynomial facts used by measure normalization. -/
def PolynomialNormalization
    (T : ℝ → ℝ → ℝ → Plane → Plane → Matrix (Fin 2) (Fin 2) ℝ → Poly → Poly) : Prop :=
  ∀ t₀ q B c u D,
    (∀ P, (T t₀ q B c u D P).totalDegree ≤ P.totalDegree) ∧
    ∀ (_hq : 0 < q) (_hB : 0 < B) (_hD : D.det ≠ 0),
      (∀ P p, MvPolynomial.eval (fun i => earlierCoordinates t₀ q B c u D p i)
        (T t₀ q B c u D P) = MvPolynomial.eval (fun i => p i) P) ∧
      ∀ K δ P S p, rawBounds K δ t₀ q B c u D P S p →
        normalizedBounds K δ (T t₀ q B c u D P) (T t₀ q B c u D S)
          (earlierCoordinates t₀ q B c u D p)

/-- The pointwise strip comparison needed in a scalar window. -/
def WindowNormalization : Prop :=
  ∀ (N χ s m t₀ q B : ℝ) (c u n center velocity : Plane)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (thickness : ℝ) (p p' : Point),
    0 < N → ‖n‖ = 1 → 0 ≤ thickness →
    |inner ℝ n (rawPlanar p - center - p 0 • velocity)| ≤ thickness →
    |inner ℝ n (rawPlanar p' - center - p' 0 • velocity)| ≤ thickness →
    |p 0 - p' 0| ≤ N ^ (-m) →
    |inner ℝ (normalTangent n) (rawPlanar p) -
      inner ℝ (normalTangent n) (rawPlanar p')| ≤ N ^ (-m) →
    |q⁻¹| + ‖Matrix.toEuclideanLin D⁻¹ (normalTangent n)‖ +
      ‖Matrix.toEuclideanLin D⁻¹ ((inner ℝ n velocity) • n - u)‖ ≤
        N ^ (m - s + χ) / 8 →
    thickness * ‖Matrix.toEuclideanLin D⁻¹ n‖ ≤ N ^ (-s + χ) / 8 →
    ‖baseProjection (earlierCoordinates t₀ q B c u D p) -
      baseProjection (earlierCoordinates t₀ q B c u D p')‖ ≤ N ^ (-s + χ)

theorem normalize_raw_support
    (T : ℝ → ℝ → ℝ → Plane → Plane → Matrix (Fin 2) (Fin 2) ℝ → Poly → Poly)
    (hT : PolynomialNormalization T) (hwindow : WindowNormalization)
    (N χ d s m : ℝ) (C : ℕ) (R : Fin C → ENNReal)
    (μ : Fin C → Measure Incidence) (b : Fin C → (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
    (h : RawSupport N χ d s m C R μ b) : Support N χ d s m C R μ b := by
  classical
  rcases h with ⟨hχ, hN, hNχ, J, w, ρ, P, S, t₀, q, B, c, u, D, tag, A, z,
    n, center, velocity, thickness, α, hw, hρ, hμ, hdom, hx, hpack, hgeom⟩
  let Φ : Fin J → Point → Point := fun e => earlierCoordinates (t₀ e) (q e) (B e) (c e) (u e) (D e)
  have hΦ (e : Fin J) : Measurable (Φ e) :=
    (continuous_earlierCoordinates _ _ _ _ _ _).measurable
  let T' : Fin J → Poly → Poly := fun e => T (t₀ e) (q e) (B e) (c e) (u e) (D e)
  refine ⟨J, (fun e => w e * ρ e Set.univ), (fun e => normalizedMap (ρ e) (Φ e)),
    (fun e => T' e (P e)), (fun e => T' e (S e)), tag, A,
    (fun a e => Φ e ∘ z a), hw, hNχ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases hρ e with ⟨hq, hB, hD, hm0, hmt, hP, hS, hdensity, hbound⟩
    rcases hT (t₀ e) (q e) (B e) (c e) (u e) (D e) with ⟨hdegree, hlocal⟩
    rcases hlocal hq hB hD with ⟨heval, hscale⟩
    refine ⟨normalizedMap_probability (ρ e) (Φ e) (hΦ e) hm0 hmt,
      (hdegree (P e)).trans hP, (hdegree (S e)).trans hS,
      earlierCoordinates_projected_ceiling (ρ e) _ _ _ _ _ _ hq hD _ hm0 hmt hdensity, ?_⟩
    exact normalizedMap_ae (ρ e) (Φ e) (hΦ e) _
      (measurableSet_normalizedBounds _ _ _ _) (hbound.mono (fun p hp => hscale _ _ _ _ _ hp))
  · intro a
    rcases hμ a with ⟨hR, htag, hA, hfull, hz⟩
    exact ⟨hR, htag, hA, hfull, fun e => (hΦ e).comp hz⟩
  · intro e
    exact weighted_maps_le_normalized (ρ e)
      (fun a => (μ a).restrict {p | p ∈ A a ∧ tag a p = e}) z R (w e) (Φ e) (hΦ e)
      (fun a => (hμ a).2.2.2.2) (hρ e).2.2.2.1 (hρ e).2.2.2.2.1 (hdom e)
  · intro a p hp
    have heval := (hT (t₀ (tag a p)) (q (tag a p)) (B (tag a p))
      (c (tag a p)) (u (tag a p)) (D (tag a p))).2
      (hρ (tag a p)).1 (hρ (tag a p)).2.1 (hρ (tag a p)).2.2.1 |>.1
    exact (hx a p hp).trans (heval (S (tag a p)) (z a p)).symm
  · intro a t y
    let I := Finset.univ.filter (fun e => ∃ p ∈ A a,
      |p.2 - t| ≤ N ^ (-m) ∧ |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e)
    obtain ⟨v, hv, hlo, hhi⟩ := hpack a t y I (fun e he => (Finset.mem_filter.mp he).2)
    exact card_le_of_mass_packing I (fun e => ρ e Set.univ) hv (Real.rpow_nonneg (by linarith) _) hlo hhi
  · intro a p hp p' hp' htag ht hy
    rcases hgeom a with ⟨hn, hth, hstrip, hframe⟩
    rcases hstrip p hp with ⟨hp0, hpY, hpstrip⟩
    rcases hstrip p' hp' with ⟨hp'0, hp'Y, hp'strip⟩
    rcases hframe (tag a p) ⟨p, hp, rfl⟩ with ⟨hdir, hnormal⟩
    apply hwindow N χ s m (t₀ (tag a p)) (q (tag a p)) (B (tag a p))
      (c (tag a p)) (u (tag a p)) (n a) (center a) (velocity a) (D (tag a p))
      (thickness a) (z a p) (z a p') (by linarith) hn hth
    · simpa only [hp0] using hpstrip
    · simpa only [hp'0] using hp'strip
    · simpa only [hp0, hp'0] using ht
    · have hdiff : inner ℝ (normalTangent (n a)) (rawPlanar (z a p)) -
          inner ℝ (normalTangent (n a)) (rawPlanar (z a p')) =
          scalarY (b a p.1) p.2 - scalarY (b a p'.1) p'.2 := by linarith
      rwa [hdiff]
    · exact hdir
    · exact hnormal

end Submission.Obl.k4_raw_earlier_witness_normalization
