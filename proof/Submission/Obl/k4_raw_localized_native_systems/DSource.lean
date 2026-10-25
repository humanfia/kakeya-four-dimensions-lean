import Submission.Obl.k4_raw_localized_native_systems.Window.SelectedRawAssembly
import Submission.Obl.k4_raw_localized_native_systems.Window.LongScaleBounds
import Submission.Obl.k4_raw_localized_native_systems.Window.DensityGood
import Submission.Obl.k4_raw_localized_native_systems.SourceFrames
import Submission.Obl.k4_raw_localized_native_systems.C.RawGeometry

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Window Pairing Packing

noncomputable section

/-- Join the analytical omission estimate and the full earlier raw laws for
one original current family. The same good sets serve every injective current
subfamily retained by positive prior and positive original world weight. -/
theorem finite_d_step {p : Data} (hp : Valid p) (hL : p.L = 1) {k M D MC DC : ℕ}
    {κ r τ χ ds s gC loss K q nw band aExp uPack uDel θ σ ζ a₀ : ℝ}
    (hχ : 0 < χ) (hpow : 2 ≤ p.N k ^ χ) (hN : 256 ≤ p.N k) (hs : s ≤ 1)
    (hκ : 1 ≤ κ) (hκK : 2 * κ ≤ K) (hK : 1 ≤ K) (hκsq : 2 * (2 * κ) ^ 2 ≤ K)
    (hKN : K ≤ p.N k) (hpriorK : p.K k ≤ K) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ wmass W e)
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ))
    (hnonempty : Nonempty (Fin (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp))).card))
    (hgood : ∀ γ z, z ∈ Good γ →
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hzero : ∀ γ z, z ∈ Good γ → p.g k γ 0 (obs (p.B k γ) 1 z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)))
    (hvel : ∀ γ z, z ∈ Good γ → ‖v z.1‖ ≤ K)
    (hGoodAng : ∀ γ z, z ∈ Good γ → AngGood p k γ uDel τ z)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (hbudget : 64 * (2 * κ) ^ 3 * p.N k ^ τ ≤ p.N k ^ χ)
    (hscale : 1 + 2 * κ ≤ p.N k ^ χ) (hKχ : p.K k ≤ p.N k ^ χ)
    (hvalue : 2 * κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : 2 * κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ))
    (hT : (2 : ℝ) ^ W.T ≤ p.N k) (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hband0 : 0 ≤ band) (hu0 : 0 ≤ uPack) (hu1 : uPack ≤ 1) (hau : aExp ≤ uPack)
    (hθ : θ ≤ 32 * p.N k ^ (-nw - band) * p.N k ^ uPack)
    (hEbound : p.N k ^ (2 * band + uPack) ≤ p.N k ^ (4 : ℕ))
    (hangleCost : 32 * (2 * κ) * p.N k ^ uPack ≤ p.N k)
    (hwindow : p.N k ^ (-(s + 4)) ≤ q)
    (hpoly : 2097152 * Real.pi * K ^ (8 + 1) ≤ p.N k ^ ζ)
    (hprofile : p.f r - p.f 0 + τ + 4 * band + 2 * uPack + ζ ≤ ds * s + χ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (hcard : ∀ γ o, ((W.lst γ o).card : ℝ) ≤ K)
    (width : Fin W.C → ℝ)
    (hexact : ∀ e, p.N k ^ (-width e) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : ∀ e, |width e - nw| ≤ band)
    (lst₁ : Fin (p.W k) → Observation →
      Finset (Fin (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp))).card)) (κ₁ : ℕ)
    (hcard₁ : ∀ γ o, (lst₁ γ o).card ≤ κ₁)
    (hmeas₁ : ∀ γ e, MeasurableSet {o | e ∈ lst₁ γ o})
    (hknown₁ : ∀ e z, z ∈ (selectWitnesses W
      (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp)))).F e →
      e ∈ lst₁ ((selectWitnesses W
        (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp)))).γ e)
        (obs (p.B k ((selectWitnesses W
          (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp)))).γ e)) (δ (p.N k) r) z))
    (hu : 0 < uDel) (huη : uDel ≤ p.η * p.L) (hθpos : 0 < θ)
    (hσ : ∀ e, minorWidth ((selectWitnesses W
      (longHeavyWitnessSet W Good (q * p.N k ^ (-aExp)))).Q e) *
      (2 * κ * (2 : ℝ) ^ W.T) ≤ σ)
    (hpin : 4 * (2 * (p.N k ^ loss * gC) + σ) / θ ≤ δ (p.N k) uDel)
    (hshort : 4 * κ * (2 : ℝ) ^ W.T * (q * p.N k ^ (-aExp)) ≤ δ (p.N k) uDel)
    (homitBound : 6 * (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Good γ)ᶜ) +
      (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
        (shortWitnessEvent W (q * p.N k ^ (-aExp)) γ)) +
      ENNReal.ofReal (p.N k ^ (-p.S * uDel + 2 * τ)) *
        ((9 * ⌈p.N k ^ loss⌉₊ * κ₁ + 9 * κ₁ : ℕ) : ENNReal) ≤
          ENNReal.ofReal (p.N k ^ (-a₀)))
    (hgC : 0 < gC) (hκCK : p.N k ^ loss ≤ K)
    (hrel : ∀ e, gC ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ)))
    (later : Atlas p k) {CC : ℕ} (γC : Fin CC → Fin (p.W k)) (n : Fin CC → Plane)
    (int sp : Fin CC → ℝ) (AC : Fin CC → Set Line) (FC : Fin CC → Set Point)
    (lstC : Fin (p.W k) → Observation → Finset (Fin CC))
    (hfam : C.CFam p k later MC DC loss gC γC n int sp AC FC lstC)
    (hanc : ∀ c z, z ∈ FC c → ∃ e, W.γ e = γC c ∧ z ∈ W.F e) :
    ∃ G : Fin CC → Set Point, (∀ c, MeasurableSet (G c)) ∧ (∀ c, G c ⊆ FC c) ∧
      (∑ c, ENNReal.ofReal (p.ω k (γC c)) * priorMass p k (γC c) (FC c \ G c)) ≤
        ENNReal.ofReal (p.N k ^ (-a₀)) ∧
      ∀ (CC' : ℕ) (ι : Fin CC' → Fin CC), Function.Injective ι →
        (∀ c, 0 < p.ν k (γC (ι c)) (AC (ι c))) →
        (∀ c, 0 < p.ω k (γC (ι c))) →
        RawSupport (p.N k) χ ds s (s + 4) CC'
          (C.cR (p.ω k) (p.ν k) (γC ∘ ι) (AC ∘ ι))
          (C.cLaws (p.ν k) (γC ∘ ι) (AC ∘ ι) (G ∘ ι))
          (C.cCoeff (p.P k) (γC ∘ ι) (n ∘ ι) (AC ∘ ι)) := by
  have hκ0 : 0 < κ := by linarith
  have hgeom := hfam.rawGeometry hgC hL
  have hcardC (γ : Fin (p.W k)) (o : Observation) :
      (lstC γ o).card ≤ ⌈p.N k ^ loss⌉₊ := by
    exact_mod_cast (hfam.2.2.2.1 γ o).trans (Nat.le_ceil _)
  obtain ⟨G, hG, hGF, hsupport, homit⟩ := exists_long_good_sets hp W hκ0 hW hr hrL hdisj Good
    hGood hGoodAng lst₁ κ₁ hcard₁ hmeas₁ hknown₁ γC FC hgeom.measurableEvents
    hgeom.originalEvents hgeom.disjointEvents lstC ⌈p.N k ^ loss⌉₊ hcardC hfam.2.2.2.2.1
    hgeom.terminalKnown n sp hfam.2.1 hgeom.normalSpeed hanc hu huη hθpos hσ hpin hshort
  refine ⟨G, hG, hGF, homit.trans homitBound, ?_⟩
  intro CC' ι hι hprior hω
  have hcoeff : C.cCoeff (p.P k) (γC ∘ ι) (n ∘ ι) (AC ∘ ι) =
      (fun c => fullTimeCoefficients (p.P k ((γC ∘ ι) c))
        (normalTangent ((n ∘ ι) c)) ((AC ∘ ι) c)) :=
    funext (fun c => C.cCoeff_eq_fullTime _ _ _ _ c)
  rw [hcoeff]
  apply raw_support_of_long_good_family hp hχ hpow hN hs hκ hκK hK hκsq hKN hpriorK
    hr hrL W hW hfloor Good hGood hnonempty hgood hzero hvel hdisj hbudget hscale hKχ
    hvalue hcurv hT hqtime hband0 hu0 hu1 hau hθ hEbound hangleCost hwindow hpoly hprofile
    hknown hcard width hexact hband (γC ∘ ι) (AC ∘ ι) (FC ∘ ι)
    (C.cLaws (p.ν k) (γC ∘ ι) (AC ∘ ι) (G ∘ ι))
    (C.cR (p.ω k) (p.ν k) (γC ∘ ι) (AC ∘ ι)) (n ∘ ι) (int ∘ ι) (sp ∘ ι)
    (fun c => hgeom.measurableEvents (ι c)) ?_ (fun c => C.cR_pos (hω c) (hprior c))
    (C.cLaws_original_domination hp _ _ _ _ hprior (fun c => hGF (ι c))) ?_
    (fun c => hfam.2.1 (ι c)) hgC.le (by positivity) hκCK
    (fun c => hgeom.assignmentTime (ι c)) (fun c => hgeom.normalStrip (ι c)) hrel
  · intro c c' hne hγ
    exact hfam.2.2.1 (ι c) (ι c') (fun h => hne (hι h)) hγ
  · apply C.cLaws_compl_eq_zero _ _ _ _ _ (fun c => hG (ι c))
    intro c z hz
    exact hsupport (ι c) hz

end
end Submission.Obl.k4_raw_localized_native_systems
