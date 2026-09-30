import Submissions.UpperLeanIsa.LengthFrameChecks

/-! Bounded scans certify every offset of both constant-biased regions. -/
namespace OptimalOTS.LengthFrameChecks
open OptimalOTS.ByteWindow OptimalOTS.HLFour

def safeRow (s e incoming declared delta : Nat) : Bool :=
  (Nat.beq s e && Nat.beq incoming declared) ||
    frameCheck bytePow s e incoming declared delta

theorem safeRow_sound {s e incoming declared delta : Nat}
    (h : safeRow s e incoming declared delta = true)
    (hw : ¬(s = e ∧ incoming = declared)) :
    frameCheck bytePow s e incoming declared delta = true := by
  simp only [safeRow, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.resolve_left hw

def scan (e declared : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | s, r :: rs => safeRow s e 1 declared r.1 &&
      safeRow s e 5504 declared r.2 && scan e declared (s+1) rs

theorem scan_sound (e declared : Nat) : ∀ rs s,
    scan e declared s rs = true → ∀ i < rs.length,
    ∀ incoming, incoming = 1 ∨ incoming = 5504 →
    ¬(s+i = e ∧ incoming = declared) →
    ∃ delta, frameCheck bytePow (s+i) e incoming declared delta = true := by
  intro rs
  induction rs with
  | nil => intros; simp_all
  | cons r rs ih =>
    intro s h i hi b hb hw
    simp only [scan, Bool.and_eq_true] at h
    cases i with
    | zero =>
      rcases hb with rfl | rfl
      · exact ⟨r.1, safeRow_sound h.1.1 (by simpa using hw)⟩
      · exact ⟨r.2, safeRow_sound h.1.2 (by simpa using hw)⟩
    | succ i =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using
        ih (s+1) h.2 i (by simpa using hi) b hb (by
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hw)

def certEntry (x : Nat) : Nat := if x < 1024 then entryOf 12 x else entF (x-1024)
def certLength (x : Nat) : Nat := if x < 1024 then SL 12 x else 68
def certBias (x : Nat) : Nat := if x < 1024 then 5504 else 1

def blocksCheck : Nat → List (List (Nat × Nat)) → Bool
  | _, [] => true
  | x, r :: rs => Nat.beq r.length (certLength x) &&
      scan (certEntry x) (certBias x) (certEntry x) r && blocksCheck (x+1) rs

theorem blocksCheck_cons {x : Nat} {r : List (Nat × Nat)} {rs : List (List (Nat × Nat))}
    (hr : r.length = certLength x ∧ scan (certEntry x) (certBias x) (certEntry x) r = true)
    (ht : blocksCheck (x+1) rs = true) : blocksCheck x (r::rs) = true := by
  simp only [blocksCheck,Bool.and_eq_true,Nat.beq_eq]
  exact ⟨hr,ht⟩

theorem blocksCheck_sound : ∀ rs x, blocksCheck x rs = true →
    ∀ j < rs.length, ∃ r, r.length = certLength (x+j) ∧
      scan (certEntry (x+j)) (certBias (x+j)) (certEntry (x+j)) r = true := by
  intro rs
  induction rs with
  | nil => intros; simp_all
  | cons r rs ih =>
    intro x h j hj
    simp only [blocksCheck, Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => exact ⟨r, h.1.1, h.1.2⟩
    | succ j =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
        ih (x+1) h.2 j (by simpa using hj)

end OptimalOTS.LengthFrameChecks
