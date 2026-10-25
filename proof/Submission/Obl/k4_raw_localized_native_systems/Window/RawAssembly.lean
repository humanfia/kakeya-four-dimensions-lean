import Submission.Obl.k4_raw_localized_native_systems.Window.RawBounds
import Submission.Obl.k4_raw_localized_native_systems.Window.RawTags

/-! Finite assembly of the raw earlier-witness certificate. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- An earlier true family and compatible full-time laws give the exact raw
certificate. All floors and packing bounds concern the entire earlier events
`H e`, before their intersections with any current event or scalar window. -/
theorem raw_support_of_family {p : Data} (hp : Valid p) {k M D : ℕ}
    {κ r τ χ d s m : ℝ} (hχ : 0 < χ) (hpow : 2 ≤ p.N k ^ χ)
    (hκ : 1 ≤ κ) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (W : Atlas p k) (H : Fin W.C → Set Point) (defaultLabel : Fin W.C)
    (hW : ∀ e, WChart p k W M D κ r e)
    (hH : ∀ e, MeasurableSet (H e)) (hHsub : ∀ e, H e ⊆ W.F e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ rawMass W H e)
    (hgood : ∀ e q, q ∈ H e →
      p.g k (W.γ e) r (obs (p.B k (W.γ e)) (δ (p.N k) r) q) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (hbudget : 64 * κ ^ 3 * p.N k ^ τ ≤ p.N k ^ χ)
    (hscale : 1 + κ ≤ p.N k ^ χ) (hK : p.K k ≤ p.N k ^ χ)
    (hvalue : κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ))
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (law : Fin C → Measure Point) (R : Fin C → ENNReal)
    (b : Fin C → Line → Fin 5 → ℝ)
    (n center velocity : Fin C → EuclideanSpace ℝ (Fin 2))
    (thickness α : Fin C → ℝ)
    (Compat : Fin C → Fin W.C → Prop)
    (hcw : ∀ a e, Compat a e → W.γ e = γC a)
    (hFC : ∀ a, MeasurableSet (FC a))
    (hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (hR : ∀ a, 0 < R a)
    (hlaw : ∀ a, R a • law a ≤
      ENNReal.ofReal (p.ω k (γC a)) • (priorMass p k (γC a)).restrict (FC a))
    (hcover : ∀ a, law a (rawSupportSet W H Compat FC a)ᶜ = 0)
    (hsignal : ∀ a q, q ∈ FC a → scalarX (b a q.1) q.2 =
      MvPolynomial.eval (x q.1 q.2) (p.P k (γC a)))
    (hgeom : ∀ a, ‖n a‖ = 1 ∧ 0 ≤ thickness a ∧
      ∀ q ∈ FC a, scalarY (b a q.1) q.2 =
        α a + inner ℝ (normalTangent (n a)) (y q.1 q.2) ∧
        |inner ℝ (n a) (y q.1 q.2 - center a - q.2 • velocity a)| ≤ thickness a)
    (hpack : ∀ a t y' (I : Finset (Fin W.C)),
      (∀ e ∈ I, ∃ q ∈ FC a, q ∈ H e ∧ Compat a e ∧ |q.2 - t| ≤ p.N k ^ (-m) ∧
        |scalarY (b a q.1) q.2 - y'| ≤ p.N k ^ (-m)) →
      ∃ v : ℝ, 0 < v ∧ (∀ e ∈ I, ENNReal.ofReal v ≤ rawMass W H e) ∧
        (∑ e ∈ I, rawMass W H e) ≤ ENNReal.ofReal (v * p.N k ^ (d * s + χ)))
    (hinv : ∀ a e, Compat a e →
      |(1 / (2 : ℝ) ^ W.T)⁻¹| +
        ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (normalTangent (n a))‖ +
        ‖Matrix.toEuclideanLin (W.Q e)⁻¹
          ((inner ℝ (n a) (velocity a)) • n a - W.u e)‖ ≤ p.N k ^ (m - s + χ) / 8 ∧
      thickness a * ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (n a)‖ ≤ p.N k ^ (-s + χ) / 8) :
    RawSupport (p.N k) χ d s m C R law b := by
  have hκ0 : 0 < κ := by linarith
  let tag := rawTag W H Compat defaultLabel
  let A := rawSupportSet W H Compat FC
  have htag (a : Fin C) (q : Point) (hq : q ∈ A a) :
      q ∈ FC a ∧ Compat a (tag a q) ∧ q ∈ H (tag a q) := by
    exact ctag_spec (rawAtlas W H) Compat defaultLabel hq
  refine ⟨hχ, hp.scale_ge_two k, hpow, W.C, (fun e => ENNReal.ofReal (p.ω k (W.γ e))),
    rawLaw W H, W.R, (fun e => p.P k (W.γ e)),
    (fun e => (W.j e : ℝ) / (2 : ℝ) ^ W.T), (fun _ => 1 / (2 : ℝ) ^ W.T),
    (fun e => p.B k (W.γ e)), W.c, W.u, W.Q, tag, A,
    (fun _ => rawGraph), n, center, velocity, thickness, α, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact raw_weighted_mass_le_one hp hW hHsub hdisj
  · intro e
    refine ⟨by positivity, hp.B_pos k (W.γ e), (hW e).det_ne, ?_, ?_,
      (hW e).R_degree, valid_P_degree hp k (W.γ e), ?_, ?_⟩
    · rw [rawLaw_mass]
      exact rawMass_pos hκ0 (hp.scale_pos k) (hW e).det_ne (hfloor e)
    · rw [rawLaw_mass]
      exact lt_top_iff_ne_top.mpr (rawMass_ne_top hp (hW e) (hHsub e))
    · exact rawLaw_base hp hκ hr hrL (hW e) (hH e) (hHsub e) (hfloor e) (hgood e) hbudget
    · exact rawLaw_ae hp (hW e) (hH e) (hHsub e)
        (native_bounds_ae hp k (W.γ e) (H e) (hH e)
          (fun q hq => ((hW e).sel (hHsub e hq)).1)) hκ hscale hK hvalue hcurv
  · intro a
    exact ⟨hR a, measurable_ctag (rawAtlas W H) Compat hH defaultLabel a,
      measurableSet_certSupport (rawAtlas W H) Compat hH hFC a,
      hcover a, measurable_rawGraph⟩
  · exact raw_tagged_domination W H hH γC FC law R Compat hcw hFC hFCdisj hlaw defaultLabel
  · intro a q hq
    have hγ := hcw a (tag a q) (htag a q hq).2.1
    change scalarX (b a q.1) q.2 = MvPolynomial.eval (x q.1 q.2) (p.P k (W.γ (tag a q)))
    rw [hγ]
    exact hsignal a q (htag a q hq).1
  · intro a t y' I hI
    have hmeet : ∀ e ∈ I, ∃ q ∈ FC a, q ∈ H e ∧ Compat a e ∧
        |q.2 - t| ≤ p.N k ^ (-m) ∧ |scalarY (b a q.1) q.2 - y'| ≤ p.N k ^ (-m) := by
      intro e he
      obtain ⟨q, hq, ht, hy, heq⟩ := hI e he
      obtain ⟨hqFC, hcompat, hqH⟩ := htag a q hq
      change tag a q = e at heq
      rw [heq] at hcompat hqH
      exact ⟨q, hqFC, hqH, hcompat, ht, hy⟩
    simpa only [rawLaw_mass, toE] using hpack a t y' I hmeet
  · intro a
    refine ⟨(hgeom a).1, (hgeom a).2.1, ?_, ?_⟩
    · intro q hq
      exact ⟨rfl, ((hgeom a).2.2 q (htag a q hq).1).1,
        ((hgeom a).2.2 q (htag a q hq).1).2⟩
    · intro e he
      obtain ⟨q, hq, hqe⟩ := he
      have hc := (htag a q hq).2.1
      change tag a q = e at hqe
      rw [hqe] at hc
      exact hinv a e hc

end
end Submission.Obl.k4_raw_localized_native_systems.Window
