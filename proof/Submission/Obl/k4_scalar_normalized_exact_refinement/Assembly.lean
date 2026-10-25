import Submission.Obl.k4_scalar_normalized_exact_refinement.Interfaces

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Stages

/-- The geometric construction, pure restriction, two density comparisons and
angular transfer leave only the tail secant calculation. -/
theorem assemble (hraw : RawRefinement) (hpure : PureRestriction)
    (hprofiles : RelativeProfiles) (hangular : AngularTransfer) : Goal := by
  intro hhom p r b h d' hp hr hrL hrb hbL hd hd1 htail hknown
  obtain ⟨q₀, hq₀, hL₀, hd₀, hS₀, hU₀, href₀⟩ :=
    hraw p r b h d' hp.1 hr hrL hrb hbL hd hd1 hknown
  obtain ⟨q, hqraw, hqpure, hLq, hdq, hSq, hUq, href⟩ :=
    hpure hhom p q₀ r b h hp.1 hq₀ hr hrL hrb hbL href₀
  have hL : L q = L p - r := hLq.trans hL₀
  have hd' : d q = d' := hdq.trans hd₀
  have hS : S q = S p := hSq.trans hS₀
  have hU : U q = U p * (L p - r) / L p := hUq.trans hU₀
  obtain ⟨hrelative, hequal⟩ :=
    hprofiles p q r b h hp hqraw hqpure hr hrL hrb hbL hL href
  obtain ⟨a, hjoint, hangle⟩ :=
    hangular p q r b h hp hqraw hqpure hr hrL hrb hbL hL hS hU href
  have hcap : TailCap q := by
    change ∀ s : ℝ, 0 ≤ s → s ≤ L q →
      f q (L q) - f q s ≤ d q * (L q - s)
    intro s hs hsL
    have hrs : r ≤ r + s := by linarith
    have hsrL : r + s ≤ L p := by linarith [hL]
    calc
      f q (L q) - f q s ≤ f p (L p) - f p (r + s) := hrelative s hs hsL
      _ ≤ d' * (L p - (r + s)) := htail (r + s) hrs hsrL
      _ = d q * (L q - s) := by rw [hd', hL]; ring
  have hqexact : Exact (withJoint q a) := ⟨hqraw, hqpure, hjoint, hcap, hangle⟩
  exact ⟨withJoint q a, hqexact, hL, hd', hS, hU, href, hrelative, hequal⟩

end Submission.Obl.k4_scalar_normalized_exact_refinement.Stages
