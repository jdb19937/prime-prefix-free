import PPF.Tree

/-!
# Sanity check against OEIS A287117

The first 61 terms of A287117 (all terms up to 535), checked by kernel evaluation.
-/

namespace PPF

theorem primePrefixFree_upto_535 :
    (Finset.Icc 1 535).filter PrimePrefixFree =
      {1, 2, 3, 4, 5, 8, 9, 16, 17, 18, 19, 32, 33, 36, 37, 64, 65, 66, 67, 72, 73,
        128, 129, 130, 131, 132, 133, 144, 145, 256, 257, 258, 259, 260, 261, 264, 265,
        266, 267, 288, 289, 290, 291, 512, 513, 516, 517, 518, 519, 520, 521, 522, 523,
        528, 529, 530, 531, 532, 533, 534, 535} := by
  decide +kernel

end PPF
