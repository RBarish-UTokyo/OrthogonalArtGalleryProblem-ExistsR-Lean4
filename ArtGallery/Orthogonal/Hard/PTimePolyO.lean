module

public import ArtGallery.Orthogonal.Hard.LowerO
public import ArtGallery.Stade.PTimePoly

/-!
# The orthogonal construction is polynomial-time

A code for the integer templates (`ITmpl`, as the pair of its denominator and vertex list) and
`fun_prop` lemmas for all functions of the construction, bottom-up, on top of those of Stade's
construction (`ArtGallery/Stade/PTimePoly.lean`): templates, input segments, the helper chains, the
copy nooks, and

* **`PT.polyO`**: `fun a => polyO (n a) (Φ a)` is polynomial-time;
* **`PT.guardsO`**.

As for Stade's polygon, every number occurring is a rational function of `H` with constant
coefficients, so the unary rational arithmetic of `ArtGallery/Stade/PTimeRat.lean` suffices; the
template data are constants.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace ArtGallery.Orthogonal.Hard

open Complexity Complexity.PT Complexity.PT.Code ArtGallery.ETRINVREV ArtGallery.Stade
  ArtGallery.Stade.Chain

/-! ### Codes -/

/-- An integer template as a pair. -/
def ITmpl.toPair (t : ITmpl) : ℕ × List (ℤ × ℤ × ℤ) := (t.D, t.pts)

/-- The integer template of a pair. -/
def ITmpl.ofPair (p : ℕ × List (ℤ × ℤ × ℤ)) : ITmpl := ⟨p.1, p.2⟩

/-- Integer templates are coded as pairs. -/
instance instCodeITmpl : Code ITmpl := Code.ofInj ITmpl.toPair ITmpl.ofPair (fun _ => rfl)

variable {α β : Type} [Code α] [Code β]

@[fun_prop] protected theorem PT.itmplPair {t : α → ITmpl} (ht : PT t) :
    PT (fun a => (t a).toPair) :=
  (PT.ofInj_to ITmpl.toPair ITmpl.ofPair (fun _ => rfl)).comp ht

@[fun_prop] protected theorem PT.itmplD {t : α → ITmpl} (ht : PT t) : PT (fun a => (t a).D) :=
  PT.fst (PT.itmplPair ht)

@[fun_prop] protected theorem PT.itmplPts {t : α → ITmpl} (ht : PT t) :
    PT (fun a => (t a).pts) :=
  PT.snd (PT.itmplPair ht)

/-- **A template instance is polynomial-time.** -/
@[fun_prop] protected theorem PT.itmplInst {H ox : α → ℚ} {t : α → ITmpl} (hH : PT H)
    (hox : PT ox) (ht : PT t) : PT (fun a => (t a).inst (H a) (ox a)) := by
  unfold ITmpl.inst
  fun_prop

/-! ### Templates -/

@[fun_prop] protected theorem PT.oTmplInputs {k : α → TKind} (hk : PT k) :
    PT (fun a => oTmplInputs (k a)) := PT.tkindFun oTmplInputs hk

@[fun_prop] protected theorem PT.oSlotFloor {k : α → TKind} (hk : PT k) :
    PT (fun a => oSlotFloor (k a)) := PT.tkindFun oSlotFloor hk

@[fun_prop] protected theorem PT.slotWsLength {k : α → TKind} (hk : PT k) :
    PT (fun a => (slotWs (k a)).length) := PT.tkindFun (fun k => (slotWs k).length) hk

@[fun_prop] protected theorem PT.oInputCeil {pos : α → Bool} (hpos : PT pos) :
    PT (fun a => oInputCeil (pos a)) := by
  refine (PT.ite hpos (PT.const (oInputCeil true)) (PT.const (oInputCeil false))).of_eq ?_
  intro a; cases pos a <;> rfl

/-! ### Inputs -/

@[fun_prop] protected theorem PT.slotInputsO {n : α → ℕ} {Φ : α → List Constraint} {c : α → ℕ}
    (hn : PT n) (hΦ : PT Φ) (hc : PT c) : PT (fun a => slotInputsO (n a) (Φ a) (c a)) := by
  unfold slotInputsO
  fun_prop

@[fun_prop] protected theorem PT.inputsO {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => inputsO (n a) (Φ a)) := by
  unfold inputsO
  fun_prop

/-! ### Helper chains and copy nooks -/

@[fun_prop] protected theorem PT.aamCanon {X Y b w ld lr lu ll : α → ℚ} (hX : PT X) (hY : PT Y)
    (hb : PT b) (hw : PT w) (hld : PT ld) (hlr : PT lr) (hlu : PT lu) (hll : PT ll) :
    PT (fun a => aamCanon (X a) (Y a) (b a) (w a) (ld a) (lr a) (lu a) (ll a)) := by
  unfold aamCanon
  fun_prop

@[fun_prop] protected theorem PT.rotL {o p : α → ℚ × ℚ} (ho : PT o) (hp : PT p) :
    PT (fun a => rotL (o a) (p a)) := by
  unfold rotL
  fun_prop

@[fun_prop] protected theorem PT.shiftQ {o p : α → ℚ × ℚ} (ho : PT o) (hp : PT p) :
    PT (fun a => shiftQ (o a) (p a)) := by
  unfold shiftQ
  fun_prop

@[fun_prop] protected theorem PT.cChain {G h d : α → ℚ} (hG : PT G) (hh : PT h) (hd : PT d) :
    PT (fun a => cChain (G a) (h a) (d a)) := by
  unfold cChain
  simp only
  fun_prop

@[fun_prop] protected theorem PT.copyNookGen {Rm Lm Nt Nb : α → ℚ × ℚ} (hRm : PT Rm)
    (hLm : PT Lm) (hNt : PT Nt) (hNb : PT Nb) :
    PT (fun a => copyNookGen (Rm a) (Lm a) (Nt a) (Nb a)) := by
  unfold copyNookGen
  simp only
  fun_prop

@[fun_prop] protected theorem PT.nookPsPt {a b : α → ℚ} {ge : α → Bool} {H : α → ℚ} (ha : PT a)
    (hb : PT b) (hge : PT ge) (hH : PT H) :
    PT (fun x => (nookPs (a x) (b x) (ge x) (H x), nookPt (a x) (b x) (ge x) (H x),
      nookTop (a x) (b x) (ge x) (H x), nookBot (a x) (b x) (ge x) (H x))) := by
  unfold nookPs nookPt nookTop nookBot nookX copyE
  fun_prop

@[fun_prop] protected theorem PT.copyNookO {a b : α → ℚ} {ge : α → Bool} {H : α → ℚ} (ha : PT a)
    (hb : PT b) (hge : PT ge) (hH : PT H) : PT (fun x => copyNookO (a x) (b x) (ge x) (H x)) := by
  have h := PT.nookPsPt ha hb hge hH
  have hPs := PT.fst h
  have hPt := PT.fst (PT.snd h)
  have hTop := PT.fst (PT.snd (PT.snd h))
  have hBot := PT.snd (PT.snd (PT.snd h))
  have hRm : PT (fun x => nookRm (a x) (b x) (ge x) (H x)) :=
    (PT.ite hge hPt hPs).of_eq fun x => by unfold nookRm; cases ge x <;> rfl
  have hLm : PT (fun x => nookLm (a x) (b x) (ge x) (H x)) :=
    (PT.ite hge hPs hPt).of_eq fun x => by unfold nookLm; cases ge x <;> rfl
  have hBotO : PT (fun x => nookBotO (a x) (b x) (ge x) (H x)) := by
    unfold nookBotO
    exact PT.pair (PT.fst hBot) (PT.ratSub (PT.snd hBot)
      (PT.ratDiv (PT.ratSub (PT.snd hTop) (PT.snd hBot)) (PT.const _)))
  exact PT.copyNookGen hRm hLm hTop hBotO

/-! ### The polygon -/

@[fun_prop] protected theorem PT.floorFeatsO {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => floorFeatsO (n a) (Φ a)) := by
  unfold floorFeatsO
  fun_prop

@[fun_prop] protected theorem PT.ceilFeatsO {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => ceilFeatsO (n a) (Φ a)) := by
  unfold ceilFeatsO
  fun_prop

/-- **The orthogonal polygon is polynomial-time.** -/
@[fun_prop] protected theorem PT.polyO {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => polyO (n a) (Φ a)) := by
  have hL := PT.xL hn hΦ
  have hR := PT.xR hn hΦ
  have hT : PT (fun a => 2 * ((paramH (n a) (Φ a) : ℕ) : ℚ)) :=
    PT.ratMul (PT.const _) (PT.ratOfNat (PT.paramH hn hΦ))
  have hl1 : PT (fun a => [(xL (n a) (Φ a), (-1 : ℚ))]) :=
    PT.cons (PT.pair hL (PT.const _)) (PT.const [])
  have hl2 : PT (fun a => [(xR (n a) (Φ a), (-1 : ℚ)), (xR (n a) (Φ a), 2 * (paramH (n a) (Φ a) : ℚ))]) :=
    PT.cons (PT.pair hR (PT.const _)) (PT.cons (PT.pair hR hT) (PT.const []))
  have hl3 : PT (fun a => [(xL (n a) (Φ a), 2 * (paramH (n a) (Φ a) : ℚ))]) :=
    PT.cons (PT.pair hL hT) (PT.const [])
  exact PT.append (PT.append (PT.append (PT.append hl1 (PT.flatten (PT.floorFeatsO hn hΦ))) hl2)
    (PT.flatten (PT.ceilFeatsO hn hΦ))) hl3

/-- The guard number of the orthogonal polygon is polynomial-time. -/
@[fun_prop] protected theorem PT.guardsO {n : α → ℕ} {Φ : α → List Constraint} (hn : PT n)
    (hΦ : PT Φ) : PT (fun a => guardsO (n a) (Φ a)) := by
  unfold guardsO
  fun_prop

end ArtGallery.Orthogonal.Hard

end
