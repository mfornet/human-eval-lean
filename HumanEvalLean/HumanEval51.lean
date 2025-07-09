import Std.Data.Iterators.Combinators.FilterMap

def is_subseq (s₁ : String) (s₂ : String) : Prop :=
    List.Sublist s₁.toList s₂.toList

def vowels : List Char := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

def no_vowels (s : String) : Prop :=
    List.all s.toList (· ∉ vowels)

def maximal_for [LE α] (P : ι → Prop) (f : ι → α) (x : ι) : Prop :=
    -- Same as MaximalFor in Mathlib
    P x ∧ ∀ y : ι, P y → f x ≤ f y → f y ≤ f x

def remove_vowels_iff (solution : String → String) : Prop :=
    (s x : String) → (solution s = x) → maximal_for (fun i => no_vowels i ∧ is_subseq i s) (String.length) x

def remove_vowels (s : String) : String :=
    String.mk (s.toList.filter (· ∉ vowels))

example : remove_vowels "abcdef" = "bcdf" := by native_decide
example : remove_vowels "abcdef\nghijklm" = "bcdf\nghjklm" := by native_decide
example : remove_vowels "aaaaa" = "" := by native_decide
example : remove_vowels "aaBAA" = "B" := by native_decide
example : remove_vowels "zbcd" = "zbcd" := by native_decide

theorem remove_vowels_correct : remove_vowels_iff remove_vowels := by
    simp [remove_vowels_iff]
    intro s
    constructor
    · simp [no_vowels, remove_vowels, is_subseq]
    · simp
      intro y hnv hss hle
      apply List.Sublist.length_le
      let hsub := List.Sublist.filter (· ∉ vowels) hss
      simp at hsub
      simp [remove_vowels]
      suffices y.data = List.filter (fun x => !decide (x ∈ vowels)) y.data by
        rwa [this]
      symm
      rw [List.filter_eq_self]
      intro a ha
      simp [no_vowels] at hnv
      simp
      exact hnv a ha

/-!
## Prompt

```python3


def remove_vowels(text):
    """
    remove_vowels is a function that takes string and returns string without vowels.
    >>> remove_vowels('')
    ''
    >>> remove_vowels("abcdef\nghijklm")
    'bcdf\nghjklm'
    >>> remove_vowels('abcdef')
    'bcdf'
    >>> remove_vowels('aaaaa')
    ''
    >>> remove_vowels('aaBAA')
    'B'
    >>> remove_vowels('zbcd')
    'zbcd'
    """
```

## Canonical solution

```python3
    return "".join([s for s in text if s.lower() not in ["a", "e", "i", "o", "u"]])
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate('') == ''
    assert candidate("abcdef\nghijklm") == 'bcdf\nghjklm'
    assert candidate('fedcba') == 'fdcb'
    assert candidate('eeeee') == ''
    assert candidate('acBAA') == 'cB'
    assert candidate('EcBOO') == 'cB'
    assert candidate('ybcd') == 'ybcd'

```
-/
