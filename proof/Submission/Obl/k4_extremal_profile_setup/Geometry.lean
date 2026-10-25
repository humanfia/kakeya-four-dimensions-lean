import Submission.Obl.k4_extremal_profile_setup.Bridges
import Submission.Obl.k4_extremal_profile_setup.Profile

namespace Submission.Obl.k4_extremal_profile_setup

def Known (p : Data) (r h : ℝ) : Prop :=
  KnownExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h

def ExactTime (p : Data) (h : ℝ) : Prop :=
  ExactTimeExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h

/-- Normalization only requires the terminal cap on the remaining interval. -/
def RemainderTransfer : Prop :=
  ∀ p : Data, p.Valid → ∀ r h q : ℝ,
    0 ≤ r → r < p.L → 0 < q → q < 1 →
    (∀ s : ℝ, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ q * (p.L - s)) →
    Known p r h → ∃ F : Data, F.Valid ∧ F.L = p.L - r ∧ F.d = q ∧
      F.S = p.S ∧ F.η = p.η ∧ horizon p ≤ h + horizon F

/-- Coarsening preserves the old profile, including its absolute offset. -/
def CoarseningComposition : Prop :=
  ∀ p : Data, p.Valid → ∀ r q U : ℝ,
    0 < r → r ≤ p.L → 0 < q → q < 1 →
    (∀ s : ℝ, 0 ≤ s → s ≤ r → p.f r - p.f s ≤ q * (r - s)) →
    0 ≤ U →
    (∀ F : Data, F.Valid → F.S = p.S → F.η = p.η → F.d ≤ p.d →
      horizon F ≤ U * F.L) →
    ∃ G : Data, G.Valid ∧ G.L = r ∧ G.d = q ∧ G.S = p.S ∧ G.η = p.η ∧
      G.f = p.f ∧ horizon p ≤ horizon G + U * (p.L - r)

def TwoSidedExtraction : Prop :=
  ∀ p : Data, p.Valid → ∀ z : ℝ, Terminal p z →
    ∃ h : ℝ, horizon p ≤ h ∧ h ≤ z ∧ ExactTime p h

def TerminalExtension : Prop :=
  ∀ d₀ S η : ℝ, d₀ < 1 → 0 < S → 0 < η →
    ∃ Cx cx : ℝ, 0 < Cx ∧ 0 < cx ∧
      ∀ p : Data, p.Valid → p.S = S → p.η = η → p.d ≤ d₀ →
        ∀ h e : ℝ, 0 < e → e < h → e < cx * p.L → ExactTime p h →
          ∃ r : ℝ, 0 < r ∧ r < p.L ∧ p.L - r ≤ Cx * e ∧ Known p r (h - e)

theorem remainderTransfer_of_expanded (ht : RemainderTransferExpanded) : RemainderTransfer := by
  intro p hp r h q hr hrL hq hq1 hcap hk
  obtain ⟨N, K, W, ω, ν, E, P, B, f, g, G, hv, hh⟩ :=
    ht p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp
      r h q hr hrL hq hq1 hcap hk
  let F : Data := ⟨N, K, p.L - r, q, p.S, p.η, W, ω, ν, E, P, B, f, g, G⟩
  refine ⟨F, hv, rfl, rfl, rfl, rfl, ?_⟩
  change HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f ≤
    h + HorizonExpanded F.N F.K F.L F.W F.ω F.ν F.E F.B F.f at hh
  simpa only [horizonExpanded_eq p, horizonExpanded_eq F] using hh

theorem coarseningComposition_of_expanded (hc : CoarseningCompositionExpanded) :
    CoarseningComposition := by
  intro p hp r q U hr hrL hq hq1 hcap hU hbound
  have hb : ∀ N K L d W ω ν E P B f g G,
      Problem N K L d p.S p.η W ω ν E P B f g G → d ≤ p.d →
        HorizonExpanded N K L W ω ν E B f ≤ U * L := by
    intro N K L d W ω ν E P B f g G hv hd
    let F : Data := ⟨N, K, L, d, p.S, p.η, W, ω, ν, E, P, B, f, g, G⟩
    change HorizonExpanded F.N F.K F.L F.W F.ω F.ν F.E F.B F.f ≤ U * F.L
    rw [horizonExpanded_eq F]
    exact hbound F hv rfl rfl hd
  obtain ⟨g, G, hv, hh⟩ :=
    hc p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp
      r q U hr hrL hq hq1 hcap hU hb
  let out : Data := {p with L := r, d := q, g := g, G := G}
  refine ⟨out, hv, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f ≤
    HorizonExpanded out.N out.K out.L out.W out.ω out.ν out.E out.B out.f + U * (p.L - r) at hh
  simpa only [horizonExpanded_eq p, horizonExpanded_eq out] using hh

theorem terminalExtension_of_expanded (hx : TerminalExtensionExpanded) : TerminalExtension := by
  intro d₀ S η hd hS hη
  obtain ⟨Cx, cx, hCx, hcx, ht⟩ := hx d₀ S η hd hS hη
  refine ⟨Cx, cx, hCx, hcx, ?_⟩
  intro p hp hpS hpη hpd h e he heh heL hex
  have hv : Problem p.N p.K p.L p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G := by
    simpa only [Data.Valid, ← hpS, ← hpη] using hp
  exact ht p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hv hpd
    h e he heh heL hex

end Submission.Obl.k4_extremal_profile_setup
