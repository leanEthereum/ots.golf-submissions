import Submissions.UpperLeanIsa.LengthBounds

namespace OptimalOTS.HLG3.LengthGate
open LeanerVM.Parameters LeanerVM.Semantics
set_option maxHeartbeats 2000000

private theorem from_block (ps : List (Nat × Nat)) (hg : ∀ p ∈ ps, Good p)
    {a k n : Nat} (hc : ps.map Prod.fst = List.range' a k)
    (hlo : a ≤ n) (hhi : n < a + k) : ∃ e, Good (n,e) := by
  have hmem : n ∈ ps.map Prod.fst := by
    rw [hc, List.mem_range']
    exact ⟨n - a, by omega, by omega⟩
  obtain ⟨⟨b,e⟩, hp, hb⟩ := List.mem_map.mp hmem
  change b = n at hb
  subst b
  exact ⟨e, hg _ hp⟩

attribute [local irreducible] block1 block129 block257 block385 block513 block641 block769 block897 block1025 block1153 block1281 block1409 block1537 block1665 block1793 block1921 block2049 block2177 block2305 block2433 block2561 block2689 block2817 block2945 block3073 block3201 block3329 block3457 block3585 block3713 block3841 block3969 block4097 block4225 block4353 block4481 block4609 block4737 block4865 block4993 block5121 block5249 block5377 block5505

theorem bounded_log {n : Nat} (h0 : 0 < n) (hn : n ≤ 5505) :
    ∃ e, gpow e = (BitVec.ofNat 64 n : K) ∧ e < ordG ∧
      (n = 5503 ∨ 2^32 ≤ (e + ordG - 4674821839435376859 + 48) % ordG) := by
  change ∃ e, Good (n,e)
  by_cases h1 : n < 129
  · exact from_block block1 block1_good block1_cover (by omega) h1
  by_cases h129 : n < 257
  · exact from_block block129 block129_good block129_cover (by omega) h129
  by_cases h257 : n < 385
  · exact from_block block257 block257_good block257_cover (by omega) h257
  by_cases h385 : n < 513
  · exact from_block block385 block385_good block385_cover (by omega) h385
  by_cases h513 : n < 641
  · exact from_block block513 block513_good block513_cover (by omega) h513
  by_cases h641 : n < 769
  · exact from_block block641 block641_good block641_cover (by omega) h641
  by_cases h769 : n < 897
  · exact from_block block769 block769_good block769_cover (by omega) h769
  by_cases h897 : n < 1025
  · exact from_block block897 block897_good block897_cover (by omega) h897
  by_cases h1025 : n < 1153
  · exact from_block block1025 block1025_good block1025_cover (by omega) h1025
  by_cases h1153 : n < 1281
  · exact from_block block1153 block1153_good block1153_cover (by omega) h1153
  by_cases h1281 : n < 1409
  · exact from_block block1281 block1281_good block1281_cover (by omega) h1281
  by_cases h1409 : n < 1537
  · exact from_block block1409 block1409_good block1409_cover (by omega) h1409
  by_cases h1537 : n < 1665
  · exact from_block block1537 block1537_good block1537_cover (by omega) h1537
  by_cases h1665 : n < 1793
  · exact from_block block1665 block1665_good block1665_cover (by omega) h1665
  by_cases h1793 : n < 1921
  · exact from_block block1793 block1793_good block1793_cover (by omega) h1793
  by_cases h1921 : n < 2049
  · exact from_block block1921 block1921_good block1921_cover (by omega) h1921
  by_cases h2049 : n < 2177
  · exact from_block block2049 block2049_good block2049_cover (by omega) h2049
  by_cases h2177 : n < 2305
  · exact from_block block2177 block2177_good block2177_cover (by omega) h2177
  by_cases h2305 : n < 2433
  · exact from_block block2305 block2305_good block2305_cover (by omega) h2305
  by_cases h2433 : n < 2561
  · exact from_block block2433 block2433_good block2433_cover (by omega) h2433
  by_cases h2561 : n < 2689
  · exact from_block block2561 block2561_good block2561_cover (by omega) h2561
  by_cases h2689 : n < 2817
  · exact from_block block2689 block2689_good block2689_cover (by omega) h2689
  by_cases h2817 : n < 2945
  · exact from_block block2817 block2817_good block2817_cover (by omega) h2817
  by_cases h2945 : n < 3073
  · exact from_block block2945 block2945_good block2945_cover (by omega) h2945
  by_cases h3073 : n < 3201
  · exact from_block block3073 block3073_good block3073_cover (by omega) h3073
  by_cases h3201 : n < 3329
  · exact from_block block3201 block3201_good block3201_cover (by omega) h3201
  by_cases h3329 : n < 3457
  · exact from_block block3329 block3329_good block3329_cover (by omega) h3329
  by_cases h3457 : n < 3585
  · exact from_block block3457 block3457_good block3457_cover (by omega) h3457
  by_cases h3585 : n < 3713
  · exact from_block block3585 block3585_good block3585_cover (by omega) h3585
  by_cases h3713 : n < 3841
  · exact from_block block3713 block3713_good block3713_cover (by omega) h3713
  by_cases h3841 : n < 3969
  · exact from_block block3841 block3841_good block3841_cover (by omega) h3841
  by_cases h3969 : n < 4097
  · exact from_block block3969 block3969_good block3969_cover (by omega) h3969
  by_cases h4097 : n < 4225
  · exact from_block block4097 block4097_good block4097_cover (by omega) h4097
  by_cases h4225 : n < 4353
  · exact from_block block4225 block4225_good block4225_cover (by omega) h4225
  by_cases h4353 : n < 4481
  · exact from_block block4353 block4353_good block4353_cover (by omega) h4353
  by_cases h4481 : n < 4609
  · exact from_block block4481 block4481_good block4481_cover (by omega) h4481
  by_cases h4609 : n < 4737
  · exact from_block block4609 block4609_good block4609_cover (by omega) h4609
  by_cases h4737 : n < 4865
  · exact from_block block4737 block4737_good block4737_cover (by omega) h4737
  by_cases h4865 : n < 4993
  · exact from_block block4865 block4865_good block4865_cover (by omega) h4865
  by_cases h4993 : n < 5121
  · exact from_block block4993 block4993_good block4993_cover (by omega) h4993
  by_cases h5121 : n < 5249
  · exact from_block block5121 block5121_good block5121_cover (by omega) h5121
  by_cases h5249 : n < 5377
  · exact from_block block5249 block5249_good block5249_cover (by omega) h5249
  by_cases h5377 : n < 5505
  · exact from_block block5377 block5377_good block5377_cover (by omega) h5377
  exact from_block block5505 block5505_good block5505_cover (by omega) (by omega)

end OptimalOTS.HLG3.LengthGate
