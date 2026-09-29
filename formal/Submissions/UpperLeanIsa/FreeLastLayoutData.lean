import Submissions.UpperLeanIsa.FreeLastLayout

/-! Generated from combined_1089.json. Every interval, block capacity, live
raw code, special hint entry, and preserved fixed region is checked by the kernel. -/
namespace OptimalOTS.FreeLastLayout
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
set_option Elab.async false

def tree0 : Tree := (.branch 431
(.branch 229
(.branch 125
(.branch 71
(.branch 53
(.branch 40
(.leaf ⟨27,13,(.group 10 126 false)⟩)
(.leaf ⟨40,13,(.group 8 159 false)⟩))
(.branch 64
(.leaf ⟨53,11,(.group 10 63 false)⟩)
(.leaf ⟨64,7,(.group 9 5 false)⟩)))
(.branch 102
(.branch 83
(.leaf ⟨71,12,(.group 9 117 false)⟩)
(.leaf ⟨83,19,(.group 10 497 false)⟩))
(.branch 118
(.leaf ⟨102,16,(.group 8 324 false)⟩)
(.leaf ⟨118,7,(.group 9 0 false)⟩))))
(.branch 185
(.branch 151
(.branch 132
(.leaf ⟨125,7,(.group 9 10 false)⟩)
(.leaf ⟨132,19,(.group 9 597 false)⟩))
(.branch 167
(.leaf ⟨151,16,(.group 10 262 false)⟩)
(.leaf ⟨167,18,(.group 8 492 false)⟩)))
(.branch 199
(.branch 192
(.leaf ⟨185,7,(.group 9 11 false)⟩)
(.leaf ⟨192,7,(.group 9 1 false)⟩))
(.branch 206
(.leaf ⟨199,7,(.group 9 7 false)⟩)
(.leaf ⟨206,23,(.group 10 1008 false)⟩)))))
(.branch 320
(.branch 281
(.branch 253
(.branch 246
(.leaf ⟨229,17,(.group 8 402 false)⟩)
(.leaf ⟨246,7,(.group 9 3 false)⟩))
(.branch 260
(.leaf ⟨253,7,(.group 9 2 false)⟩)
(.leaf ⟨260,21,(.group 9 854 false)⟩)))
(.branch 306
(.branch 293
(.leaf ⟨281,12,(.group 10 98 false)⟩)
(.leaf ⟨293,13,(.group 8 157 false)⟩))
(.branch 313
(.leaf ⟨306,7,(.group 9 4 false)⟩)
(.leaf ⟨313,7,(.group 9 8 false)⟩))))
(.branch 373
(.branch 357
(.branch 335
(.leaf ⟨320,15,(.group 9 258 false)⟩)
(.leaf ⟨335,22,(.group 10 858 false)⟩))
(.branch 366
(.leaf ⟨357,9,(.group 8 58 false)⟩)
(.leaf ⟨366,7,(.group 9 9 false)⟩)))
(.branch 400
(.branch 380
(.leaf ⟨373,7,(.group 9 6 false)⟩)
(.leaf ⟨380,20,(.group 9 716 false)⟩))
(.branch 424
(.leaf ⟨400,24,(.group 10 1023 false)⟩)
(.leaf ⟨424,7,(.group 8 5 false)⟩))))))
(.branch 648
(.branch 525
(.branch 478
(.branch 447
(.branch 439
(.leaf ⟨431,8,(.group 9 18 false)⟩)
(.leaf ⟨439,8,(.group 9 20 false)⟩))
(.branch 456
(.leaf ⟨447,9,(.group 9 35 false)⟩)
(.leaf ⟨456,22,(.group 10 857 false)⟩)))
(.branch 499
(.branch 491
(.leaf ⟨478,13,(.group 10 125 false)⟩)
(.leaf ⟨491,8,(.group 9 21 false)⟩))
(.branch 507
(.leaf ⟨499,8,(.group 9 19 false)⟩)
(.leaf ⟨507,18,(.group 9 492 false)⟩))))
(.branch 591
(.branch 555
(.branch 542
(.leaf ⟨525,17,(.group 8 401 false)⟩)
(.leaf ⟨542,13,(.group 10 124 false)⟩))
(.branch 571
(.leaf ⟨555,16,(.group 9 322 false)⟩)
(.leaf ⟨571,20,(.group 10 602 false)⟩)))
(.branch 619
(.branch 603
(.leaf ⟨591,12,(.group 8 121 false)⟩)
(.leaf ⟨603,16,(.group 10 261 false)⟩))
(.branch 629
(.leaf ⟨619,10,(.group 9 65 false)⟩)
(.leaf ⟨629,19,(.group 10 496 false)⟩)))))
(.branch 776
(.branch 712
(.branch 683
(.branch 671
(.leaf ⟨648,23,(.group 10 1007 false)⟩)
(.leaf ⟨671,12,(.group 10 97 false)⟩))
(.branch 691
(.leaf ⟨683,8,(.group 9 23 false)⟩)
(.leaf ⟨691,21,(.group 10 722 false)⟩)))
(.branch 747
(.branch 733
(.leaf ⟨712,21,(.group 10 721 false)⟩)
(.leaf ⟨733,14,(.group 10 162 false)⟩))
(.branch 756
(.leaf ⟨747,9,(.group 9 34 false)⟩)
(.leaf ⟨756,20,(.group 10 601 false)⟩))))
(.branch 837
(.branch 807
(.branch 800
(.leaf ⟨776,24,(.group 10 1022 false)⟩)
(.leaf ⟨800,7,(.group 8 0 false)⟩))
(.branch 815
(.leaf ⟨807,8,(.group 8 21 false)⟩)
(.leaf ⟨815,22,(.group 10 856 false)⟩)))
(.branch 882
(.branch 859
(.leaf ⟨837,22,(.group 10 855 false)⟩)
(.leaf ⟨859,23,(.group 10 1006 false)⟩))
(.branch 902
(.leaf ⟨882,20,(.group 10 600 false)⟩)
(.leaf ⟨902,22,(.group 10 854 false)⟩)))))))

theorem tree0_checked : tree0.check 27 924 = true := by decide +kernel

def tree1 : Tree := (.branch 1523
(.branch 1211
(.branch 1061
(.branch 1002
(.branch 969
(.branch 946
(.leaf ⟨924,22,(.group 10 853 false)⟩)
(.leaf ⟨946,23,(.group 10 1005 false)⟩))
(.branch 993
(.leaf ⟨969,24,(.group 10 1021 false)⟩)
(.leaf ⟨993,9,(.group 10 38 false)⟩)))
(.branch 1027
(.branch 1019
(.leaf ⟨1002,17,(.group 9 402 false)⟩)
(.leaf ⟨1019,8,(.group 9 22 false)⟩))
(.branch 1046
(.leaf ⟨1027,19,(.group 9 596 false)⟩)
(.leaf ⟨1046,15,(.group 8 258 false)⟩))))
(.branch 1131
(.branch 1087
(.branch 1077
(.leaf ⟨1061,16,(.group 8 323 false)⟩)
(.leaf ⟨1077,10,(.group 8 73 false)⟩))
(.branch 1108
(.leaf ⟨1087,21,(.group 9 853 false)⟩)
(.leaf ⟨1108,23,(.group 10 1004 false)⟩)))
(.branch 1166
(.branch 1147
(.leaf ⟨1131,16,(.group 10 260 false)⟩)
(.leaf ⟨1147,19,(.group 9 598 false)⟩))
(.branch 1190
(.leaf ⟨1166,24,(.group 10 1020 false)⟩)
(.leaf ⟨1190,21,(.group 10 720 false)⟩)))))
(.branch 1354
(.branch 1288
(.branch 1252
(.branch 1231
(.leaf ⟨1211,20,(.group 9 717 false)⟩)
(.leaf ⟨1231,21,(.group 10 719 false)⟩))
(.branch 1275
(.leaf ⟨1252,23,(.group 10 1003 false)⟩)
(.leaf ⟨1275,13,(.group 9 157 false)⟩)))
(.branch 1333
(.branch 1309
(.leaf ⟨1288,21,(.group 10 718 false)⟩)
(.leaf ⟨1309,24,(.group 10 1019 false)⟩))
(.branch 1334
(.leaf ⟨1333,1,.trap⟩)
(.leaf ⟨1334,20,(.group 8 717 false)⟩))))
(.branch 1445
(.branch 1400
(.branch 1378
(.leaf ⟨1354,24,(.group 10 1018 false)⟩)
(.leaf ⟨1378,22,(.group 10 852 false)⟩))
(.branch 1423
(.leaf ⟨1400,23,(.group 10 1002 false)⟩)
(.leaf ⟨1423,22,(.group 10 851 false)⟩)))
(.branch 1483
(.branch 1467
(.leaf ⟨1445,22,(.group 10 850 false)⟩)
(.leaf ⟨1467,16,(.group 10 259 false)⟩))
(.branch 1501
(.leaf ⟨1483,18,(.group 10 406 false)⟩)
(.leaf ⟨1501,22,(.group 10 849 false)⟩))))))
(.branch 1853
(.branch 1693
(.branch 1601
(.branch 1553
(.branch 1533
(.leaf ⟨1523,10,(.group 9 60 false)⟩)
(.leaf ⟨1533,20,(.group 10 599 false)⟩))
(.branch 1577
(.leaf ⟨1553,24,(.group 10 1017 false)⟩)
(.leaf ⟨1577,24,(.group 10 1016 false)⟩)))
(.branch 1648
(.branch 1625
(.leaf ⟨1601,24,(.group 10 1015 false)⟩)
(.leaf ⟨1625,23,(.group 10 1001 false)⟩))
(.branch 1670
(.leaf ⟨1648,22,(.group 10 848 false)⟩)
(.leaf ⟨1670,23,(.group 10 1000 false)⟩))))
(.branch 1773
(.branch 1740
(.branch 1717
(.leaf ⟨1693,24,(.group 10 1014 false)⟩)
(.leaf ⟨1717,23,(.group 10 999 false)⟩))
(.branch 1761
(.leaf ⟨1740,21,(.group 10 717 false)⟩)
(.leaf ⟨1761,12,(.group 10 96 false)⟩)))
(.branch 1813
(.branch 1791
(.leaf ⟨1773,18,(.group 10 405 false)⟩)
(.leaf ⟨1791,22,(.group 10 847 false)⟩))
(.branch 1834
(.leaf ⟨1813,21,(.group 10 716 false)⟩)
(.leaf ⟨1834,19,(.group 10 495 false)⟩)))))
(.branch 2024
(.branch 1938
(.branch 1891
(.branch 1872
(.leaf ⟨1853,19,(.group 10 494 false)⟩)
(.leaf ⟨1872,19,(.group 10 493 false)⟩))
(.branch 1915
(.leaf ⟨1891,24,(.group 10 1013 false)⟩)
(.leaf ⟨1915,23,(.group 10 998 false)⟩)))
(.branch 1976
(.branch 1960
(.leaf ⟨1938,22,(.group 10 846 false)⟩)
(.leaf ⟨1960,16,(.group 10 258 false)⟩))
(.branch 2000
(.leaf ⟨1976,24,(.group 10 1012 false)⟩)
(.leaf ⟨2000,24,(.group 10 1011 false)⟩))))
(.branch 2087
(.branch 2052
(.branch 2032
(.leaf ⟨2024,8,(.group 8 18 false)⟩)
(.leaf ⟨2032,20,(.group 9 718 false)⟩))
(.branch 2073
(.leaf ⟨2052,21,(.group 8 863 false)⟩)
(.leaf ⟨2073,14,(.group 10 161 false)⟩)))
(.branch 2119
(.branch 2095
(.leaf ⟨2087,8,(.group 8 23 false)⟩)
(.leaf ⟨2095,24,(.group 10 1010 false)⟩))
(.branch 2127
(.leaf ⟨2119,8,(.group 8 25 false)⟩)
(.leaf ⟨2127,24,(.group 10 1009 false)⟩)))))))

theorem tree1_checked : tree1.check 924 2151 = true := by decide +kernel

def tree2 : Tree := (.branch 2724
(.branch 2429
(.branch 2275
(.branch 2211
(.branch 2181
(.branch 2158
(.leaf ⟨2151,7,(.group 8 7 false)⟩)
(.leaf ⟨2158,23,(.group 10 997 false)⟩))
(.branch 2190
(.leaf ⟨2181,9,(.group 8 59 false)⟩)
(.leaf ⟨2190,21,(.group 10 715 false)⟩)))
(.branch 2246
(.branch 2232
(.leaf ⟨2211,21,(.group 8 865 false)⟩)
(.leaf ⟨2232,14,(.group 10 160 false)⟩))
(.branch 2260
(.leaf ⟨2246,14,(.group 8 204 false)⟩)
(.leaf ⟨2260,15,(.group 10 207 false)⟩))))
(.branch 2348
(.branch 2302
(.branch 2285
(.leaf ⟨2275,10,(.group 8 74 false)⟩)
(.leaf ⟨2285,17,(.group 10 328 false)⟩))
(.branch 2325
(.leaf ⟨2302,23,(.group 10 996 false)⟩)
(.leaf ⟨2325,23,(.group 10 995 false)⟩)))
(.branch 2393
(.branch 2371
(.leaf ⟨2348,23,(.group 10 994 false)⟩)
(.leaf ⟨2371,22,(.group 10 845 false)⟩))
(.branch 2410
(.leaf ⟨2393,17,(.group 10 327 false)⟩)
(.leaf ⟨2410,19,(.group 10 492 false)⟩)))))
(.branch 2558
(.branch 2480
(.branch 2445
(.branch 2437
(.leaf ⟨2429,8,(.group 10 26 false)⟩)
(.leaf ⟨2437,8,(.group 8 20 false)⟩))
(.branch 2464
(.leaf ⟨2445,19,(.group 10 491 false)⟩)
(.leaf ⟨2464,16,(.group 10 257 false)⟩)))
(.branch 2526
(.branch 2503
(.leaf ⟨2480,23,(.group 10 993 false)⟩)
(.leaf ⟨2503,23,(.group 10 992 false)⟩))
(.branch 2542
(.leaf ⟨2526,16,(.group 10 256 false)⟩)
(.leaf ⟨2542,16,(.group 8 325 false)⟩))))
(.branch 2639
(.branch 2595
(.branch 2580
(.leaf ⟨2558,22,(.group 10 844 false)⟩)
(.leaf ⟨2580,15,(.group 10 206 false)⟩))
(.branch 2616
(.leaf ⟨2595,21,(.group 10 714 false)⟩)
(.leaf ⟨2616,23,(.group 10 991 false)⟩)))
(.branch 2681
(.branch 2658
(.leaf ⟨2639,19,(.group 10 490 false)⟩)
(.leaf ⟨2658,23,(.group 10 990 false)⟩))
(.branch 2704
(.leaf ⟨2681,23,(.group 10 989 false)⟩)
(.leaf ⟨2704,20,(.group 10 598 false)⟩))))))
(.branch 3043
(.branch 2884
(.branch 2802
(.branch 2765
(.branch 2743
(.leaf ⟨2724,19,(.group 10 489 false)⟩)
(.leaf ⟨2743,22,(.group 10 843 false)⟩))
(.branch 2782
(.leaf ⟨2765,17,(.group 10 326 false)⟩)
(.leaf ⟨2782,20,(.group 10 597 false)⟩)))
(.branch 2845
(.branch 2824
(.leaf ⟨2802,22,(.group 10 842 false)⟩)
(.leaf ⟨2824,21,(.group 10 713 false)⟩))
(.branch 2862
(.leaf ⟨2845,17,(.group 10 325 false)⟩)
(.leaf ⟨2862,22,(.group 10 841 false)⟩))))
(.branch 2963
(.branch 2921
(.branch 2903
(.leaf ⟨2884,19,(.group 10 488 false)⟩)
(.leaf ⟨2903,18,(.group 10 404 false)⟩))
(.branch 2941
(.leaf ⟨2921,20,(.group 10 596 false)⟩)
(.leaf ⟨2941,22,(.group 10 840 false)⟩)))
(.branch 3006
(.branch 2983
(.leaf ⟨2963,20,(.group 10 595 false)⟩)
(.leaf ⟨2983,23,(.group 10 988 false)⟩))
(.branch 3027
(.leaf ⟨3006,21,(.group 10 712 false)⟩)
(.leaf ⟨3027,16,(.group 10 255 false)⟩)))))
(.branch 3188
(.branch 3113
(.branch 3076
(.branch 3055
(.leaf ⟨3043,12,(.group 8 123 false)⟩)
(.leaf ⟨3055,21,(.group 10 711 false)⟩))
(.branch 3093
(.leaf ⟨3076,17,(.group 8 403 false)⟩)
(.leaf ⟨3093,20,(.group 10 594 false)⟩)))
(.branch 3146
(.branch 3129
(.leaf ⟨3113,16,(.group 10 254 false)⟩)
(.leaf ⟨3129,17,(.group 10 324 false)⟩))
(.branch 3169
(.leaf ⟨3146,23,(.group 10 987 false)⟩)
(.leaf ⟨3169,19,(.group 10 487 false)⟩))))
(.branch 3277
(.branch 3232
(.branch 3209
(.leaf ⟨3188,21,(.group 10 710 false)⟩)
(.leaf ⟨3209,23,(.group 10 986 false)⟩))
(.branch 3254
(.leaf ⟨3232,22,(.group 10 839 false)⟩)
(.leaf ⟨3254,23,(.group 10 985 false)⟩)))
(.branch 3314
(.branch 3296
(.leaf ⟨3277,19,(.group 10 486 false)⟩)
(.leaf ⟨3296,18,(.group 10 403 false)⟩))
(.branch 3334
(.leaf ⟨3314,20,(.group 10 593 false)⟩)
(.leaf ⟨3334,22,(.group 10 838 false)⟩)))))))

theorem tree2_checked : tree2.check 2151 3356 = true := by decide +kernel

def tree3 : Tree := (.branch 3992
(.branch 3671
(.branch 3510
(.branch 3436
(.branch 3393
(.branch 3376
(.leaf ⟨3356,20,(.group 10 592 false)⟩)
(.leaf ⟨3376,17,(.group 10 323 false)⟩))
(.branch 3414
(.leaf ⟨3393,21,(.group 10 709 false)⟩)
(.leaf ⟨3414,22,(.group 10 837 false)⟩)))
(.branch 3470
(.branch 3458
(.leaf ⟨3436,22,(.group 10 836 false)⟩)
(.leaf ⟨3458,12,(.group 10 95 false)⟩))
(.branch 3488
(.leaf ⟨3470,18,(.group 10 402 false)⟩)
(.leaf ⟨3488,22,(.group 10 835 false)⟩))))
(.branch 3592
(.branch 3552
(.branch 3533
(.leaf ⟨3510,23,(.group 10 984 false)⟩)
(.leaf ⟨3533,19,(.group 10 485 false)⟩))
(.branch 3573
(.leaf ⟨3552,21,(.group 10 708 false)⟩)
(.leaf ⟨3573,19,(.group 10 484 false)⟩)))
(.branch 3636
(.branch 3614
(.leaf ⟨3592,22,(.group 10 834 false)⟩)
(.leaf ⟨3614,22,(.group 10 833 false)⟩))
(.branch 3654
(.leaf ⟨3636,18,(.group 10 401 false)⟩)
(.leaf ⟨3654,17,(.group 10 322 false)⟩)))))
(.branch 3833
(.branch 3751
(.branch 3710
(.branch 3693
(.leaf ⟨3671,22,(.group 10 832 false)⟩)
(.leaf ⟨3693,17,(.group 10 321 false)⟩))
(.branch 3733
(.leaf ⟨3710,23,(.group 10 983 false)⟩)
(.leaf ⟨3733,18,(.group 10 400 false)⟩)))
(.branch 3793
(.branch 3774
(.leaf ⟨3751,23,(.group 10 982 false)⟩)
(.leaf ⟨3774,19,(.group 10 483 false)⟩))
(.branch 3816
(.leaf ⟨3793,23,(.group 10 981 false)⟩)
(.leaf ⟨3816,17,(.group 10 320 false)⟩))))
(.branch 3919
(.branch 3876
(.branch 3854
(.leaf ⟨3833,21,(.group 10 707 false)⟩)
(.leaf ⟨3854,22,(.group 10 831 false)⟩))
(.branch 3898
(.leaf ⟨3876,22,(.group 10 830 false)⟩)
(.leaf ⟨3898,21,(.group 10 706 false)⟩)))
(.branch 3957
(.branch 3941
(.leaf ⟨3919,22,(.group 10 829 false)⟩)
(.leaf ⟨3941,16,(.group 10 253 false)⟩))
(.branch 3974
(.leaf ⟨3957,17,(.group 10 319 false)⟩)
(.leaf ⟨3974,18,(.group 10 399 false)⟩))))))
(.branch 4236
(.branch 4105
(.branch 4064
(.branch 4028
(.branch 4012
(.leaf ⟨3992,20,(.group 10 591 false)⟩)
(.leaf ⟨4012,16,(.group 10 252 false)⟩))
(.branch 4046
(.leaf ⟨4028,18,(.group 10 398 false)⟩)
(.leaf ⟨4046,18,(.group 10 397 false)⟩)))
(.branch 4084
(.branch 4075
(.leaf ⟨4064,11,(.group 10 62 false)⟩)
(.leaf ⟨4075,9,(.group 9 33 false)⟩))
(.branch 4094
(.leaf ⟨4084,10,(.group 9 63 false)⟩)
(.leaf ⟨4094,11,(.group 9 91 false)⟩))))
(.branch 4169
(.branch 4148
(.branch 4126
(.leaf ⟨4105,21,(.group 10 705 false)⟩)
(.leaf ⟨4126,22,(.group 10 828 false)⟩))
(.branch 4158
(.leaf ⟨4148,10,(.group 9 61 false)⟩)
(.leaf ⟨4158,11,(.group 9 89 false)⟩)))
(.branch 4208
(.branch 4186
(.leaf ⟨4169,17,(.group 10 318 false)⟩)
(.leaf ⟨4186,22,(.group 10 827 false)⟩))
(.branch 4218
(.leaf ⟨4208,10,(.group 9 64 false)⟩)
(.leaf ⟨4218,18,(.group 9 491 false)⟩)))))
(.branch 4343
(.branch 4287
(.branch 4266
(.branch 4258
(.leaf ⟨4236,22,(.group 10 826 false)⟩)
(.leaf ⟨4258,8,(.group 10 25 false)⟩))
(.branch 4276
(.leaf ⟨4266,10,(.group 9 62 false)⟩)
(.leaf ⟨4276,11,(.group 9 90 false)⟩)))
(.branch 4324
(.branch 4302
(.leaf ⟨4287,15,(.group 9 257 false)⟩)
(.leaf ⟨4302,22,(.group 10 825 false)⟩))
(.branch 4331
(.leaf ⟨4324,7,(.group 8 6 false)⟩)
(.leaf ⟨4331,12,(.group 9 118 false)⟩))))
(.branch 4406
(.branch 4387
(.branch 4364
(.leaf ⟨4343,21,(.group 9 852 false)⟩)
(.leaf ⟨4364,23,(.group 10 980 false)⟩))
(.branch 4394
(.leaf ⟨4387,7,(.group 8 1 false)⟩)
(.leaf ⟨4394,12,(.group 9 119 false)⟩)))
(.branch 4443
(.branch 4420
(.leaf ⟨4406,14,(.group 9 201 false)⟩)
(.leaf ⟨4420,23,(.group 10 979 false)⟩))
(.branch 4457
(.leaf ⟨4443,14,(.group 10 159 false)⟩)
(.leaf ⟨4457,17,(.group 9 401 false)⟩)))))))

theorem tree3_checked : tree3.check 3356 4474 = true := by decide +kernel

def tree4 : Tree := (.branch 5070
(.branch 4735
(.branch 4618
(.branch 4540
(.branch 4518
(.branch 4497
(.leaf ⟨4474,23,(.group 10 978 false)⟩)
(.leaf ⟨4497,21,(.group 10 704 false)⟩))
(.branch 4525
(.leaf ⟨4518,7,(.group 8 2 false)⟩)
(.leaf ⟨4525,15,(.group 9 256 false)⟩)))
(.branch 4585
(.branch 4563
(.leaf ⟨4540,23,(.group 10 977 false)⟩)
(.leaf ⟨4563,22,(.group 10 824 false)⟩))
(.branch 4601
(.leaf ⟨4585,16,(.group 9 324 false)⟩)
(.leaf ⟨4601,17,(.group 10 317 false)⟩))))
(.branch 4674
(.branch 4644
(.branch 4637
(.leaf ⟨4618,19,(.group 10 482 false)⟩)
(.leaf ⟨4637,7,(.group 7 0 false)⟩))
(.branch 4651
(.leaf ⟨4644,7,(.group 8 3 false)⟩)
(.leaf ⟨4651,23,(.group 10 976 false)⟩)))
(.branch 4707
(.branch 4687
(.leaf ⟨4674,13,(.group 10 123 false)⟩)
(.leaf ⟨4687,20,(.group 10 590 false)⟩))
(.branch 4718
(.leaf ⟨4707,11,(.group 8 93 false)⟩)
(.leaf ⟨4718,17,(.group 10 316 false)⟩)))))
(.branch 4906
(.branch 4819
(.branch 4778
(.branch 4755
(.leaf ⟨4735,20,(.group 10 589 false)⟩)
(.leaf ⟨4755,23,(.group 10 975 false)⟩))
(.branch 4799
(.leaf ⟨4778,21,(.group 10 703 false)⟩)
(.leaf ⟨4799,20,(.group 10 588 false)⟩)))
(.branch 4862
(.branch 4840
(.leaf ⟨4819,21,(.group 10 702 false)⟩)
(.leaf ⟨4840,22,(.group 10 823 false)⟩))
(.branch 4884
(.leaf ⟨4862,22,(.group 10 822 false)⟩)
(.leaf ⟨4884,22,(.group 10 821 false)⟩))))
(.branch 4986
(.branch 4943
(.branch 4923
(.leaf ⟨4906,17,(.group 10 315 false)⟩)
(.leaf ⟨4923,20,(.group 10 587 false)⟩))
(.branch 4966
(.leaf ⟨4943,23,(.group 10 974 false)⟩)
(.leaf ⟨4966,20,(.group 10 586 false)⟩)))
(.branch 5025
(.branch 5009
(.leaf ⟨4986,23,(.group 10 973 false)⟩)
(.leaf ⟨5009,16,(.group 10 251 false)⟩))
(.branch 5048
(.leaf ⟨5025,23,(.group 10 972 false)⟩)
(.leaf ⟨5048,22,(.group 10 820 false)⟩))))))
(.branch 5382
(.branch 5230
(.branch 5150
(.branch 5113
(.branch 5091
(.leaf ⟨5070,21,(.group 10 701 false)⟩)
(.leaf ⟨5091,22,(.group 10 819 false)⟩))
(.branch 5127
(.leaf ⟨5113,14,(.group 9 202 false)⟩)
(.leaf ⟨5127,23,(.group 10 971 false)⟩)))
(.branch 5188
(.branch 5173
(.leaf ⟨5150,23,(.group 10 970 false)⟩)
(.leaf ⟨5173,15,(.group 8 257 false)⟩))
(.branch 5209
(.leaf ⟨5188,21,(.group 10 700 false)⟩)
(.leaf ⟨5209,21,(.group 10 699 false)⟩))))
(.branch 5306
(.branch 5266
(.branch 5253
(.leaf ⟨5230,23,(.group 10 969 false)⟩)
(.leaf ⟨5253,13,(.group 10 122 false)⟩))
(.branch 5286
(.leaf ⟨5266,20,(.group 10 585 false)⟩)
(.leaf ⟨5286,20,(.group 10 584 false)⟩)))
(.branch 5346
(.branch 5324
(.leaf ⟨5306,18,(.group 10 396 false)⟩)
(.leaf ⟨5324,22,(.group 10 818 false)⟩))
(.branch 5365
(.leaf ⟨5346,19,(.group 10 481 false)⟩)
(.leaf ⟨5365,17,(.group 10 314 false)⟩)))))
(.branch 5553
(.branch 5464
(.branch 5426
(.branch 5405
(.leaf ⟨5382,23,(.group 10 968 false)⟩)
(.leaf ⟨5405,21,(.group 10 698 false)⟩))
(.branch 5449
(.leaf ⟨5426,23,(.group 10 967 false)⟩)
(.leaf ⟨5449,15,(.group 10 205 false)⟩)))
(.branch 5508
(.branch 5486
(.leaf ⟨5464,22,(.group 10 817 false)⟩)
(.leaf ⟨5486,22,(.group 10 816 false)⟩))
(.branch 5530
(.leaf ⟨5508,22,(.group 10 815 false)⟩)
(.leaf ⟨5530,23,(.group 10 966 false)⟩))))
(.branch 5638
(.branch 5597
(.branch 5574
(.leaf ⟨5553,21,(.group 10 697 false)⟩)
(.leaf ⟨5574,23,(.group 10 965 false)⟩))
(.branch 5618
(.leaf ⟨5597,21,(.group 10 696 false)⟩)
(.leaf ⟨5618,20,(.group 10 583 false)⟩)))
(.branch 5680
(.branch 5658
(.leaf ⟨5638,20,(.group 10 582 false)⟩)
(.leaf ⟨5658,22,(.group 10 814 false)⟩))
(.branch 5693
(.leaf ⟨5680,13,(.group 10 121 false)⟩)
(.leaf ⟨5693,19,(.group 10 480 false)⟩)))))))

theorem tree4_checked : tree4.check 4474 5712 = true := by decide +kernel

def tree5 : Tree := (.branch 6328
(.branch 6025
(.branch 5865
(.branch 5781
(.branch 5739
(.branch 5729
(.leaf ⟨5712,17,(.group 10 313 false)⟩)
(.leaf ⟨5729,10,(.group 10 48 false)⟩))
(.branch 5762
(.leaf ⟨5739,23,(.group 10 964 false)⟩)
(.leaf ⟨5762,19,(.group 10 479 false)⟩)))
(.branch 5824
(.branch 5804
(.leaf ⟨5781,23,(.group 10 963 false)⟩)
(.leaf ⟨5804,20,(.group 10 581 false)⟩))
(.branch 5842
(.leaf ⟨5824,18,(.group 10 395 false)⟩)
(.leaf ⟨5842,23,(.group 10 962 false)⟩))))
(.branch 5938
(.branch 5906
(.branch 5888
(.leaf ⟨5865,23,(.group 10 961 false)⟩)
(.leaf ⟨5888,18,(.group 10 394 false)⟩))
(.branch 5924
(.leaf ⟨5906,18,(.group 10 393 false)⟩)
(.leaf ⟨5924,14,(.group 10 158 false)⟩)))
(.branch 5980
(.branch 5957
(.leaf ⟨5938,19,(.group 10 478 false)⟩)
(.leaf ⟨5957,23,(.group 10 960 false)⟩))
(.branch 6002
(.leaf ⟨5980,22,(.group 10 813 false)⟩)
(.leaf ⟨6002,23,(.group 10 959 false)⟩)))))
(.branch 6179
(.branch 6108
(.branch 6062
(.branch 6040
(.leaf ⟨6025,15,(.group 10 204 false)⟩)
(.leaf ⟨6040,22,(.group 10 812 false)⟩))
(.branch 6085
(.leaf ⟨6062,23,(.group 10 958 false)⟩)
(.leaf ⟨6085,23,(.group 10 957 false)⟩)))
(.branch 6151
(.branch 6130
(.leaf ⟨6108,22,(.group 10 811 false)⟩)
(.leaf ⟨6130,21,(.group 10 695 false)⟩))
(.branch 6169
(.leaf ⟨6151,18,(.group 10 392 false)⟩)
(.leaf ⟨6169,10,(.group 10 47 false)⟩))))
(.branch 6247
(.branch 6214
(.branch 6191
(.leaf ⟨6179,12,(.group 8 122 false)⟩)
(.leaf ⟨6191,23,(.group 10 956 false)⟩))
(.branch 6231
(.leaf ⟨6214,17,(.group 10 312 false)⟩)
(.leaf ⟨6231,16,(.group 10 250 false)⟩)))
(.branch 6289
(.branch 6268
(.leaf ⟨6247,21,(.group 10 694 false)⟩)
(.leaf ⟨6268,21,(.group 10 693 false)⟩))
(.branch 6309
(.leaf ⟨6289,20,(.group 10 580 false)⟩)
(.leaf ⟨6309,19,(.group 8 599 false)⟩))))))
(.branch 6634
(.branch 6490
(.branch 6410
(.branch 6371
(.branch 6349
(.leaf ⟨6328,21,(.group 10 692 false)⟩)
(.leaf ⟨6349,22,(.group 10 810 false)⟩))
(.branch 6387
(.leaf ⟨6371,16,(.group 10 249 false)⟩)
(.leaf ⟨6387,23,(.group 10 955 false)⟩)))
(.branch 6448
(.branch 6430
(.leaf ⟨6410,20,(.group 10 579 false)⟩)
(.leaf ⟨6430,18,(.group 10 391 false)⟩))
(.branch 6471
(.leaf ⟨6448,23,(.group 10 954 false)⟩)
(.leaf ⟨6471,19,(.group 10 477 false)⟩))))
(.branch 6559
(.branch 6521
(.branch 6501
(.leaf ⟨6490,11,(.group 10 61 false)⟩)
(.leaf ⟨6501,20,(.group 10 578 false)⟩))
(.branch 6542
(.leaf ⟨6521,21,(.group 10 691 false)⟩)
(.leaf ⟨6542,17,(.group 10 311 false)⟩)))
(.branch 6591
(.branch 6570
(.leaf ⟨6559,11,(.group 10 60 false)⟩)
(.leaf ⟨6570,21,(.group 10 690 false)⟩))
(.branch 6614
(.leaf ⟨6591,23,(.group 10 953 false)⟩)
(.leaf ⟨6614,20,(.group 10 577 false)⟩)))))
(.branch 6783
(.branch 6705
(.branch 6665
(.branch 6646
(.leaf ⟨6634,12,(.group 10 94 false)⟩)
(.leaf ⟨6646,19,(.group 10 476 false)⟩))
(.branch 6688
(.leaf ⟨6665,23,(.group 10 952 false)⟩)
(.leaf ⟨6688,17,(.group 10 310 false)⟩)))
(.branch 6745
(.branch 6728
(.leaf ⟨6705,23,(.group 10 951 false)⟩)
(.leaf ⟨6728,17,(.group 10 309 false)⟩))
(.branch 6768
(.leaf ⟨6745,23,(.group 10 950 false)⟩)
(.leaf ⟨6768,15,(.group 10 203 false)⟩))))
(.branch 6855
(.branch 6820
(.branch 6805
(.leaf ⟨6783,22,(.group 10 809 false)⟩)
(.leaf ⟨6805,15,(.group 10 202 false)⟩))
(.branch 6834
(.leaf ⟨6820,14,(.group 10 157 false)⟩)
(.leaf ⟨6834,21,(.group 10 689 false)⟩)))
(.branch 6898
(.branch 6877
(.leaf ⟨6855,22,(.group 10 808 false)⟩)
(.leaf ⟨6877,21,(.group 10 688 false)⟩))
(.branch 6917
(.leaf ⟨6898,19,(.group 10 475 false)⟩)
(.leaf ⟨6917,23,(.group 10 949 false)⟩)))))))

theorem tree5_checked : tree5.check 5712 6940 = true := by decide +kernel

def tree6 : Tree := (.branch 7604
(.branch 7266
(.branch 7111
(.branch 7027
(.branch 6982
(.branch 6961
(.leaf ⟨6940,21,(.group 10 687 false)⟩)
(.leaf ⟨6961,21,(.group 10 686 false)⟩))
(.branch 7004
(.leaf ⟨6982,22,(.group 10 807 false)⟩)
(.leaf ⟨7004,23,(.group 10 948 false)⟩)))
(.branch 7069
(.branch 7046
(.leaf ⟨7027,19,(.group 10 474 false)⟩)
(.leaf ⟨7046,23,(.group 10 947 false)⟩))
(.branch 7089
(.leaf ⟨7069,20,(.group 10 576 false)⟩)
(.leaf ⟨7089,22,(.group 10 806 false)⟩))))
(.branch 7192
(.branch 7148
(.branch 7127
(.leaf ⟨7111,16,(.group 10 248 false)⟩)
(.leaf ⟨7127,21,(.group 10 685 false)⟩))
(.branch 7171
(.leaf ⟨7148,23,(.group 10 946 false)⟩)
(.leaf ⟨7171,21,(.group 10 684 false)⟩)))
(.branch 7229
(.branch 7208
(.leaf ⟨7192,16,(.group 10 247 false)⟩)
(.leaf ⟨7208,21,(.group 10 683 false)⟩))
(.branch 7252
(.leaf ⟨7229,23,(.group 10 945 false)⟩)
(.leaf ⟨7252,14,(.group 10 156 false)⟩)))))
(.branch 7436
(.branch 7354
(.branch 7312
(.branch 7289
(.leaf ⟨7266,23,(.group 10 944 false)⟩)
(.leaf ⟨7289,23,(.group 10 943 false)⟩))
(.branch 7333
(.leaf ⟨7312,21,(.group 10 682 false)⟩)
(.leaf ⟨7333,21,(.group 10 681 false)⟩)))
(.branch 7390
(.branch 7374
(.leaf ⟨7354,20,(.group 10 575 false)⟩)
(.leaf ⟨7374,16,(.group 10 246 false)⟩))
(.branch 7413
(.leaf ⟨7390,23,(.group 10 942 false)⟩)
(.leaf ⟨7413,23,(.group 10 941 false)⟩))))
(.branch 7519
(.branch 7481
(.branch 7458
(.leaf ⟨7436,22,(.group 10 805 false)⟩)
(.leaf ⟨7458,23,(.group 10 940 false)⟩))
(.branch 7496
(.leaf ⟨7481,15,(.group 10 201 false)⟩)
(.leaf ⟨7496,23,(.group 10 939 false)⟩)))
(.branch 7561
(.branch 7540
(.leaf ⟨7519,21,(.group 10 680 false)⟩)
(.leaf ⟨7540,21,(.group 10 679 false)⟩))
(.branch 7582
(.leaf ⟨7561,21,(.group 10 678 false)⟩)
(.leaf ⟨7582,22,(.group 10 804 false)⟩))))))
(.branch 7944
(.branch 7774
(.branch 7688
(.branch 7644
(.branch 7621
(.leaf ⟨7604,17,(.group 10 308 false)⟩)
(.leaf ⟨7621,23,(.group 10 938 false)⟩))
(.branch 7666
(.leaf ⟨7644,22,(.group 10 803 false)⟩)
(.leaf ⟨7666,22,(.group 10 802 false)⟩)))
(.branch 7733
(.branch 7710
(.leaf ⟨7688,22,(.group 10 801 false)⟩)
(.leaf ⟨7710,23,(.group 10 937 false)⟩))
(.branch 7754
(.leaf ⟨7733,21,(.group 10 677 false)⟩)
(.leaf ⟨7754,20,(.group 10 574 false)⟩))))
(.branch 7859
(.branch 7819
(.branch 7796
(.leaf ⟨7774,22,(.group 10 800 false)⟩)
(.leaf ⟨7796,23,(.group 10 936 false)⟩))
(.branch 7841
(.leaf ⟨7819,22,(.group 10 799 false)⟩)
(.leaf ⟨7841,18,(.group 10 390 false)⟩)))
(.branch 7902
(.branch 7881
(.leaf ⟨7859,22,(.group 10 798 false)⟩)
(.leaf ⟨7881,21,(.group 10 676 false)⟩))
(.branch 7923
(.leaf ⟨7902,21,(.group 10 675 false)⟩)
(.leaf ⟨7923,21,(.group 10 674 false)⟩)))))
(.branch 8110
(.branch 8028
(.branch 7989
(.branch 7966
(.leaf ⟨7944,22,(.group 10 797 false)⟩)
(.leaf ⟨7966,23,(.group 10 935 false)⟩))
(.branch 8010
(.leaf ⟨7989,21,(.group 10 673 false)⟩)
(.leaf ⟨8010,18,(.group 10 389 false)⟩)))
(.branch 8068
(.branch 8046
(.leaf ⟨8028,18,(.group 8 494 false)⟩)
(.leaf ⟨8046,22,(.group 10 796 false)⟩))
(.branch 8090
(.leaf ⟨8068,22,(.group 10 795 false)⟩)
(.leaf ⟨8090,20,(.group 10 573 false)⟩))))
(.branch 8180
(.branch 8152
(.branch 8129
(.leaf ⟨8110,19,(.group 10 473 false)⟩)
(.leaf ⟨8129,23,(.group 10 934 false)⟩))
(.branch 8167
(.leaf ⟨8152,15,(.group 10 200 false)⟩)
(.leaf ⟨8167,13,(.group 9 155 false)⟩)))
(.branch 8218
(.branch 8198
(.leaf ⟨8180,18,(.group 9 493 false)⟩)
(.leaf ⟨8198,20,(.group 10 572 false)⟩))
(.branch 8232
(.leaf ⟨8218,14,(.group 10 155 false)⟩)
(.leaf ⟨8232,14,(.group 9 200 false)⟩)))))))

theorem tree6_checked : tree6.check 6940 8246 = true := by decide +kernel

def tree7 : Tree := (.branch 8833
(.branch 8531
(.branch 8372
(.branch 8311
(.branch 8282
(.branch 8263
(.leaf ⟨8246,17,(.group 9 400 false)⟩)
(.leaf ⟨8263,19,(.group 10 472 false)⟩))
(.branch 8295
(.leaf ⟨8282,13,(.group 10 120 false)⟩)
(.leaf ⟨8295,16,(.group 9 323 false)⟩)))
(.branch 8346
(.branch 8325
(.leaf ⟨8311,14,(.group 10 154 false)⟩)
(.leaf ⟨8325,21,(.group 10 672 false)⟩))
(.branch 8359
(.leaf ⟨8346,13,(.group 10 119 false)⟩)
(.leaf ⟨8359,13,(.group 9 156 false)⟩))))
(.branch 8459
(.branch 8414
(.branch 8393
(.leaf ⟨8372,21,(.group 10 671 false)⟩)
(.leaf ⟨8393,21,(.group 10 670 false)⟩))
(.branch 8436
(.leaf ⟨8414,22,(.group 10 794 false)⟩)
(.leaf ⟨8436,23,(.group 10 933 false)⟩)))
(.branch 8491
(.branch 8482
(.leaf ⟨8459,23,(.group 10 932 false)⟩)
(.leaf ⟨8482,9,(.group 8 57 false)⟩))
(.branch 8510
(.leaf ⟨8491,19,(.group 10 471 false)⟩)
(.leaf ⟨8510,21,(.group 10 669 false)⟩)))))
(.branch 8663
(.branch 8589
(.branch 8555
(.branch 8547
(.leaf ⟨8531,16,(.group 10 245 false)⟩)
(.leaf ⟨8547,8,(.group 8 26 false)⟩))
(.branch 8577
(.leaf ⟨8555,22,(.group 10 793 false)⟩)
(.leaf ⟨8577,12,(.group 10 93 false)⟩)))
(.branch 8630
(.branch 8608
(.leaf ⟨8589,19,(.group 10 470 false)⟩)
(.leaf ⟨8608,22,(.group 10 792 false)⟩))
(.branch 8647
(.leaf ⟨8630,17,(.group 10 307 false)⟩)
(.leaf ⟨8647,16,(.group 10 244 false)⟩))))
(.branch 8745
(.branch 8707
(.branch 8686
(.leaf ⟨8663,23,(.group 10 931 false)⟩)
(.leaf ⟨8686,21,(.group 10 668 false)⟩))
(.branch 8726
(.leaf ⟨8707,19,(.group 8 597 false)⟩)
(.leaf ⟨8726,19,(.group 10 469 false)⟩)))
(.branch 8790
(.branch 8768
(.leaf ⟨8745,23,(.group 10 930 false)⟩)
(.leaf ⟨8768,22,(.group 10 791 false)⟩))
(.branch 8812
(.leaf ⟨8790,22,(.group 10 790 false)⟩)
(.leaf ⟨8812,21,(.group 10 667 false)⟩))))))
(.branch 9149
(.branch 8990
(.branch 8912
(.branch 8872
(.branch 8853
(.leaf ⟨8833,20,(.group 10 571 false)⟩)
(.leaf ⟨8853,19,(.group 10 468 false)⟩))
(.branch 8892
(.leaf ⟨8872,20,(.group 10 570 false)⟩)
(.leaf ⟨8892,20,(.group 10 569 false)⟩)))
(.branch 8950
(.branch 8929
(.leaf ⟨8912,17,(.group 10 306 false)⟩)
(.leaf ⟨8929,21,(.group 10 666 false)⟩))
(.branch 8970
(.leaf ⟨8950,20,(.group 10 568 false)⟩)
(.leaf ⟨8970,20,(.group 10 567 false)⟩))))
(.branch 9072
(.branch 9029
(.branch 9013
(.leaf ⟨8990,23,(.group 10 929 false)⟩)
(.leaf ⟨9013,16,(.group 10 243 false)⟩))
(.branch 9050
(.leaf ⟨9029,21,(.group 10 665 false)⟩)
(.leaf ⟨9050,22,(.group 10 789 false)⟩)))
(.branch 9113
(.branch 9095
(.leaf ⟨9072,23,(.group 10 928 false)⟩)
(.leaf ⟨9095,18,(.group 10 388 false)⟩))
(.branch 9135
(.leaf ⟨9113,22,(.group 10 788 false)⟩)
(.leaf ⟨9135,14,(.group 10 153 false)⟩)))))
(.branch 9310
(.branch 9233
(.branch 9192
(.branch 9172
(.leaf ⟨9149,23,(.group 10 927 false)⟩)
(.leaf ⟨9172,20,(.group 10 566 false)⟩))
(.branch 9214
(.leaf ⟨9192,22,(.group 10 787 false)⟩)
(.leaf ⟨9214,19,(.group 10 467 false)⟩)))
(.branch 9275
(.branch 9255
(.leaf ⟨9233,22,(.group 10 786 false)⟩)
(.leaf ⟨9255,20,(.group 10 565 false)⟩))
(.branch 9296
(.leaf ⟨9275,21,(.group 10 664 false)⟩)
(.leaf ⟨9296,14,(.group 10 152 false)⟩))))
(.branch 9382
(.branch 9351
(.branch 9329
(.leaf ⟨9310,19,(.group 10 466 false)⟩)
(.leaf ⟨9329,22,(.group 10 785 false)⟩))
(.branch 9372
(.leaf ⟨9351,21,(.group 10 663 false)⟩)
(.leaf ⟨9372,10,(.group 10 46 false)⟩)))
(.branch 9422
(.branch 9400
(.leaf ⟨9382,18,(.group 8 493 false)⟩)
(.leaf ⟨9400,22,(.group 10 784 false)⟩))
(.branch 9445
(.leaf ⟨9422,23,(.group 10 926 false)⟩)
(.leaf ⟨9445,7,(.group 8 4 false)⟩)))))))

theorem tree7_checked : tree7.check 8246 9452 = true := by decide +kernel

def tree8 : Tree := (.branch 10095
(.branch 9764
(.branch 9595
(.branch 9528
(.branch 9487
(.branch 9469
(.leaf ⟨9452,17,(.group 10 305 false)⟩)
(.leaf ⟨9469,18,(.group 10 387 false)⟩))
(.branch 9509
(.leaf ⟨9487,22,(.group 10 783 false)⟩)
(.leaf ⟨9509,19,(.group 10 465 false)⟩)))
(.branch 9567
(.branch 9548
(.leaf ⟨9528,20,(.group 10 564 false)⟩)
(.leaf ⟨9548,19,(.group 10 464 false)⟩))
(.branch 9583
(.leaf ⟨9567,16,(.group 10 242 false)⟩)
(.leaf ⟨9583,12,(.group 10 92 false)⟩))))
(.branch 9677
(.branch 9636
(.branch 9616
(.leaf ⟨9595,21,(.group 10 662 false)⟩)
(.leaf ⟨9616,20,(.group 10 563 false)⟩))
(.branch 9655
(.leaf ⟨9636,19,(.group 10 463 false)⟩)
(.leaf ⟨9655,22,(.group 10 782 false)⟩)))
(.branch 9720
(.branch 9697
(.leaf ⟨9677,20,(.group 10 562 false)⟩)
(.leaf ⟨9697,23,(.group 10 925 false)⟩))
(.branch 9743
(.leaf ⟨9720,23,(.group 10 924 false)⟩)
(.leaf ⟨9743,21,(.group 10 661 false)⟩)))))
(.branch 9935
(.branch 9849
(.branch 9808
(.branch 9785
(.leaf ⟨9764,21,(.group 10 660 false)⟩)
(.leaf ⟨9785,23,(.group 10 923 false)⟩))
(.branch 9827
(.leaf ⟨9808,19,(.group 10 462 false)⟩)
(.leaf ⟨9827,22,(.group 10 781 false)⟩)))
(.branch 9894
(.branch 9871
(.leaf ⟨9849,22,(.group 10 780 false)⟩)
(.leaf ⟨9871,23,(.group 10 922 false)⟩))
(.branch 9913
(.leaf ⟨9894,19,(.group 10 461 false)⟩)
(.leaf ⟨9913,22,(.group 10 779 false)⟩))))
(.branch 10018
(.branch 9976
(.branch 9955
(.leaf ⟨9935,20,(.group 10 561 false)⟩)
(.leaf ⟨9955,21,(.group 10 659 false)⟩))
(.branch 9997
(.leaf ⟨9976,21,(.group 10 658 false)⟩)
(.leaf ⟨9997,21,(.group 10 657 false)⟩)))
(.branch 10057
(.branch 10041
(.leaf ⟨10018,23,(.group 10 921 false)⟩)
(.leaf ⟨10041,16,(.group 10 241 false)⟩))
(.branch 10078
(.leaf ⟨10057,21,(.group 10 656 false)⟩)
(.leaf ⟨10078,17,(.group 10 304 false)⟩))))))
(.branch 10417
(.branch 10262
(.branch 10182
(.branch 10141
(.branch 10118
(.leaf ⟨10095,23,(.group 10 920 false)⟩)
(.leaf ⟨10118,23,(.group 10 919 false)⟩))
(.branch 10164
(.leaf ⟨10141,23,(.group 10 918 false)⟩)
(.leaf ⟨10164,18,(.group 10 386 false)⟩)))
(.branch 10222
(.branch 10201
(.leaf ⟨10182,19,(.group 10 460 false)⟩)
(.leaf ⟨10201,21,(.group 10 655 false)⟩))
(.branch 10239
(.leaf ⟨10222,17,(.group 10 303 false)⟩)
(.leaf ⟨10239,23,(.group 10 917 false)⟩))))
(.branch 10334
(.branch 10304
(.branch 10282
(.leaf ⟨10262,20,(.group 10 560 false)⟩)
(.leaf ⟨10282,22,(.group 10 778 false)⟩))
(.branch 10316
(.leaf ⟨10304,12,(.group 10 91 false)⟩)
(.leaf ⟨10316,18,(.group 10 385 false)⟩)))
(.branch 10373
(.branch 10350
(.leaf ⟨10334,16,(.group 10 240 false)⟩)
(.leaf ⟨10350,23,(.group 10 916 false)⟩))
(.branch 10396
(.leaf ⟨10373,23,(.group 10 915 false)⟩)
(.leaf ⟨10396,21,(.group 10 654 false)⟩)))))
(.branch 10570
(.branch 10500
(.branch 10457
(.branch 10440
(.leaf ⟨10417,23,(.group 10 914 false)⟩)
(.leaf ⟨10440,17,(.group 10 302 false)⟩))
(.branch 10479
(.leaf ⟨10457,22,(.group 10 777 false)⟩)
(.leaf ⟨10479,21,(.group 10 653 false)⟩)))
(.branch 10532
(.branch 10512
(.leaf ⟨10500,12,(.group 10 90 false)⟩)
(.leaf ⟨10512,20,(.group 10 559 false)⟩))
(.branch 10548
(.leaf ⟨10532,16,(.group 10 239 false)⟩)
(.leaf ⟨10548,22,(.group 10 776 false)⟩))))
(.branch 10643
(.branch 10601
(.branch 10585
(.leaf ⟨10570,15,(.group 10 199 false)⟩)
(.leaf ⟨10585,16,(.group 10 238 false)⟩))
(.branch 10624
(.leaf ⟨10601,23,(.group 10 913 false)⟩)
(.leaf ⟨10624,19,(.group 10 459 false)⟩)))
(.branch 10687
(.branch 10665
(.leaf ⟨10643,22,(.group 10 775 false)⟩)
(.leaf ⟨10665,22,(.group 10 774 false)⟩))
(.branch 10710
(.leaf ⟨10687,23,(.group 10 912 false)⟩)
(.leaf ⟨10710,20,(.group 10 558 false)⟩)))))))

theorem tree8_checked : tree8.check 9452 10730 = true := by decide +kernel

def tree9 : Tree := (.branch 11384
(.branch 11065
(.branch 10901
(.branch 10814
(.branch 10774
(.branch 10753
(.leaf ⟨10730,23,(.group 10 911 false)⟩)
(.leaf ⟨10753,21,(.group 10 652 false)⟩))
(.branch 10796
(.leaf ⟨10774,22,(.group 10 773 false)⟩)
(.leaf ⟨10796,18,(.group 10 384 false)⟩)))
(.branch 10860
(.branch 10837
(.leaf ⟨10814,23,(.group 10 910 false)⟩)
(.leaf ⟨10837,23,(.group 10 909 false)⟩))
(.branch 10883
(.leaf ⟨10860,23,(.group 10 908 false)⟩)
(.leaf ⟨10883,18,(.group 10 383 false)⟩))))
(.branch 10984
(.branch 10942
(.branch 10922
(.leaf ⟨10901,21,(.group 10 651 false)⟩)
(.leaf ⟨10922,20,(.group 10 557 false)⟩))
(.branch 10965
(.leaf ⟨10942,23,(.group 10 907 false)⟩)
(.leaf ⟨10965,19,(.group 10 458 false)⟩)))
(.branch 11026
(.branch 11007
(.leaf ⟨10984,23,(.group 10 906 false)⟩)
(.leaf ⟨11007,19,(.group 10 457 false)⟩))
(.branch 11048
(.leaf ⟨11026,22,(.group 10 772 false)⟩)
(.leaf ⟨11048,17,(.group 10 301 false)⟩)))))
(.branch 11222
(.branch 11146
(.branch 11109
(.branch 11086
(.leaf ⟨11065,21,(.group 10 650 false)⟩)
(.leaf ⟨11086,23,(.group 10 905 false)⟩))
(.branch 11128
(.leaf ⟨11109,19,(.group 10 456 false)⟩)
(.leaf ⟨11128,18,(.group 10 382 false)⟩)))
(.branch 11183
(.branch 11166
(.leaf ⟨11146,20,(.group 10 556 false)⟩)
(.leaf ⟨11166,17,(.group 10 300 false)⟩))
(.branch 11206
(.leaf ⟨11183,23,(.group 10 904 false)⟩)
(.leaf ⟨11206,16,(.group 10 237 false)⟩))))
(.branch 11305
(.branch 11260
(.branch 11239
(.leaf ⟨11222,17,(.group 10 299 false)⟩)
(.leaf ⟨11239,21,(.group 10 649 false)⟩))
(.branch 11283
(.leaf ⟨11260,23,(.group 10 903 false)⟩)
(.leaf ⟨11283,22,(.group 10 771 false)⟩)))
(.branch 11345
(.branch 11328
(.leaf ⟨11305,23,(.group 10 902 false)⟩)
(.leaf ⟨11328,17,(.group 10 298 false)⟩))
(.branch 11363
(.leaf ⟨11345,18,(.group 10 381 false)⟩)
(.leaf ⟨11363,21,(.group 10 648 false)⟩))))))
(.branch 11702
(.branch 11540
(.branch 11463
(.branch 11426
(.branch 11404
(.leaf ⟨11384,20,(.group 10 555 false)⟩)
(.leaf ⟨11404,22,(.group 10 770 false)⟩))
(.branch 11441
(.leaf ⟨11426,15,(.group 10 198 false)⟩)
(.leaf ⟨11441,22,(.group 10 769 false)⟩)))
(.branch 11504
(.branch 11484
(.leaf ⟨11463,21,(.group 10 647 false)⟩)
(.leaf ⟨11484,20,(.group 10 554 false)⟩))
(.branch 11519
(.leaf ⟨11504,15,(.group 10 197 false)⟩)
(.leaf ⟨11519,21,(.group 10 646 false)⟩))))
(.branch 11617
(.branch 11584
(.branch 11562
(.leaf ⟨11540,22,(.group 10 768 false)⟩)
(.leaf ⟨11562,22,(.group 10 767 false)⟩))
(.branch 11594
(.leaf ⟨11584,10,(.group 10 45 false)⟩)
(.leaf ⟨11594,23,(.group 10 901 false)⟩)))
(.branch 11659
(.branch 11638
(.leaf ⟨11617,21,(.group 10 645 false)⟩)
(.leaf ⟨11638,21,(.group 10 644 false)⟩))
(.branch 11681
(.leaf ⟨11659,22,(.group 10 766 false)⟩)
(.leaf ⟨11681,21,(.group 10 643 false)⟩)))))
(.branch 11871
(.branch 11791
(.branch 11747
(.branch 11725
(.leaf ⟨11702,23,(.group 10 900 false)⟩)
(.leaf ⟨11725,22,(.group 10 765 false)⟩))
(.branch 11770
(.leaf ⟨11747,23,(.group 10 899 false)⟩)
(.leaf ⟨11770,21,(.group 10 642 false)⟩)))
(.branch 11834
(.branch 11811
(.leaf ⟨11791,20,(.group 10 553 false)⟩)
(.leaf ⟨11811,23,(.group 10 898 false)⟩))
(.branch 11849
(.leaf ⟨11834,15,(.group 10 196 false)⟩)
(.leaf ⟨11849,22,(.group 10 764 false)⟩))))
(.branch 11951
(.branch 11913
(.branch 11890
(.leaf ⟨11871,19,(.group 10 455 false)⟩)
(.leaf ⟨11890,23,(.group 10 897 false)⟩))
(.branch 11932
(.leaf ⟨11913,19,(.group 10 454 false)⟩)
(.leaf ⟨11932,19,(.group 10 453 false)⟩)))
(.branch 11996
(.branch 11973
(.leaf ⟨11951,22,(.group 10 763 false)⟩)
(.leaf ⟨11973,23,(.group 10 896 false)⟩))
(.branch 12019
(.leaf ⟨11996,23,(.group 10 895 false)⟩)
(.leaf ⟨12019,23,(.group 10 894 false)⟩)))))))

theorem tree9_checked : tree9.check 10730 12042 = true := by decide +kernel

def tree10 : Tree := (.branch 12646
(.branch 12328
(.branch 12200
(.branch 12117
(.branch 12086
(.branch 12064
(.leaf ⟨12042,22,(.group 10 762 false)⟩)
(.leaf ⟨12064,22,(.group 10 761 false)⟩))
(.branch 12103
(.leaf ⟨12086,17,(.group 10 297 false)⟩)
(.leaf ⟨12103,14,(.group 10 151 false)⟩)))
(.branch 12157
(.branch 12139
(.leaf ⟨12117,22,(.group 10 760 false)⟩)
(.leaf ⟨12139,18,(.group 10 380 false)⟩))
(.branch 12179
(.leaf ⟨12157,22,(.group 10 759 false)⟩)
(.leaf ⟨12179,21,(.group 10 641 false)⟩))))
(.branch 12265
(.branch 12242
(.branch 12223
(.leaf ⟨12200,23,(.group 10 893 false)⟩)
(.leaf ⟨12223,19,(.group 10 452 false)⟩))
(.branch 12255
(.leaf ⟨12242,13,(.group 10 118 false)⟩)
(.leaf ⟨12255,10,(.group 8 72 false)⟩)))
(.branch 12300
(.branch 12282
(.leaf ⟨12265,17,(.group 10 296 false)⟩)
(.leaf ⟨12282,18,(.group 10 379 false)⟩))
(.branch 12320
(.leaf ⟨12300,20,(.group 10 552 false)⟩)
(.leaf ⟨12320,8,(.group 8 19 false)⟩)))))
(.branch 12485
(.branch 12411
(.branch 12373
(.branch 12351
(.leaf ⟨12328,23,(.group 10 892 false)⟩)
(.leaf ⟨12351,22,(.group 10 758 false)⟩))
(.branch 12393
(.leaf ⟨12373,20,(.group 10 551 false)⟩)
(.leaf ⟨12393,18,(.group 10 378 false)⟩)))
(.branch 12447
(.branch 12429
(.leaf ⟨12411,18,(.group 10 377 false)⟩)
(.leaf ⟨12429,18,(.group 10 376 false)⟩))
(.branch 12467
(.leaf ⟨12447,20,(.group 8 719 false)⟩)
(.leaf ⟨12467,18,(.group 10 375 false)⟩))))
(.branch 12573
(.branch 12528
(.branch 12508
(.leaf ⟨12485,23,(.group 10 891 false)⟩)
(.leaf ⟨12508,20,(.group 10 550 false)⟩))
(.branch 12551
(.leaf ⟨12528,23,(.group 10 890 false)⟩)
(.leaf ⟨12551,22,(.group 10 757 false)⟩)))
(.branch 12613
(.branch 12591
(.leaf ⟨12573,18,(.group 10 374 false)⟩)
(.leaf ⟨12591,22,(.group 10 756 false)⟩))
(.branch 12634
(.leaf ⟨12613,21,(.group 10 640 false)⟩)
(.leaf ⟨12634,12,(.group 10 89 false)⟩))))))
(.branch 12959
(.branch 12785
(.branch 12709
(.branch 12673
(.branch 12654
(.leaf ⟨12646,8,(.group 8 24 false)⟩)
(.leaf ⟨12654,19,(.group 10 451 false)⟩))
(.branch 12688
(.leaf ⟨12673,15,(.group 10 195 false)⟩)
(.leaf ⟨12688,21,(.group 10 639 false)⟩)))
(.branch 12743
(.branch 12726
(.leaf ⟨12709,17,(.group 10 295 false)⟩)
(.leaf ⟨12726,17,(.group 10 294 false)⟩))
(.branch 12766
(.leaf ⟨12743,23,(.group 10 889 false)⟩)
(.leaf ⟨12766,19,(.group 10 450 false)⟩))))
(.branch 12872
(.branch 12827
(.branch 12806
(.leaf ⟨12785,21,(.group 10 638 false)⟩)
(.leaf ⟨12806,21,(.group 10 637 false)⟩))
(.branch 12849
(.leaf ⟨12827,22,(.group 10 755 false)⟩)
(.leaf ⟨12849,23,(.group 10 888 false)⟩)))
(.branch 12916
(.branch 12894
(.leaf ⟨12872,22,(.group 10 754 false)⟩)
(.leaf ⟨12894,22,(.group 10 753 false)⟩))
(.branch 12938
(.leaf ⟨12916,22,(.group 10 752 false)⟩)
(.leaf ⟨12938,21,(.group 10 636 false)⟩)))))
(.branch 13116
(.branch 13038
(.branch 12999
(.branch 12980
(.leaf ⟨12959,21,(.group 10 635 false)⟩)
(.leaf ⟨12980,19,(.group 10 449 false)⟩))
(.branch 13018
(.leaf ⟨12999,19,(.group 10 448 false)⟩)
(.leaf ⟨13018,20,(.group 10 549 false)⟩)))
(.branch 13077
(.branch 13056
(.leaf ⟨13038,18,(.group 10 373 false)⟩)
(.leaf ⟨13056,21,(.group 10 634 false)⟩))
(.branch 13097
(.leaf ⟨13077,20,(.group 10 548 false)⟩)
(.leaf ⟨13097,19,(.group 10 447 false)⟩))))
(.branch 13200
(.branch 13154
(.branch 13138
(.leaf ⟨13116,22,(.group 10 751 false)⟩)
(.leaf ⟨13138,16,(.group 10 236 false)⟩))
(.branch 13177
(.leaf ⟨13154,23,(.group 10 887 false)⟩)
(.leaf ⟨13177,23,(.group 10 886 false)⟩)))
(.branch 13242
(.branch 13221
(.leaf ⟨13200,21,(.group 10 633 false)⟩)
(.leaf ⟨13221,21,(.group 10 632 false)⟩))
(.branch 13265
(.leaf ⟨13242,23,(.group 10 885 false)⟩)
(.leaf ⟨13265,21,(.group 10 631 false)⟩)))))))

theorem tree10_checked : tree10.check 12042 13286 = true := by decide +kernel

def tree11 : Tree := (.branch 13950
(.branch 13618
(.branch 13452
(.branch 13372
(.branch 13332
(.branch 13309
(.leaf ⟨13286,23,(.group 10 884 false)⟩)
(.leaf ⟨13309,23,(.group 10 883 false)⟩))
(.branch 13349
(.leaf ⟨13332,17,(.group 10 293 false)⟩)
(.leaf ⟨13349,23,(.group 10 882 false)⟩)))
(.branch 13410
(.branch 13392
(.leaf ⟨13372,20,(.group 10 547 false)⟩)
(.leaf ⟨13392,18,(.group 10 372 false)⟩))
(.branch 13429
(.leaf ⟨13410,19,(.group 10 446 false)⟩)
(.leaf ⟨13429,23,(.group 10 881 false)⟩))))
(.branch 13532
(.branch 13497
(.branch 13474
(.leaf ⟨13452,22,(.group 10 750 false)⟩)
(.leaf ⟨13474,23,(.group 10 880 false)⟩))
(.branch 13519
(.leaf ⟨13497,22,(.group 10 749 false)⟩)
(.leaf ⟨13519,13,(.group 10 117 false)⟩)))
(.branch 13577
(.branch 13554
(.leaf ⟨13532,22,(.group 10 748 false)⟩)
(.leaf ⟨13554,23,(.group 10 879 false)⟩))
(.branch 13596
(.leaf ⟨13577,19,(.group 10 445 false)⟩)
(.leaf ⟨13596,22,(.group 10 747 false)⟩)))))
(.branch 13787
(.branch 13707
(.branch 13661
(.branch 13638
(.leaf ⟨13618,20,(.group 10 546 false)⟩)
(.leaf ⟨13638,23,(.group 10 878 false)⟩))
(.branch 13684
(.leaf ⟨13661,23,(.group 10 877 false)⟩)
(.leaf ⟨13684,23,(.group 10 876 false)⟩)))
(.branch 13742
(.branch 13727
(.leaf ⟨13707,20,(.group 10 545 false)⟩)
(.leaf ⟨13727,15,(.group 10 194 false)⟩))
(.branch 13764
(.leaf ⟨13742,22,(.group 10 746 false)⟩)
(.leaf ⟨13764,23,(.group 10 875 false)⟩))))
(.branch 13867
(.branch 13828
(.branch 13807
(.leaf ⟨13787,20,(.group 10 544 false)⟩)
(.leaf ⟨13807,21,(.group 10 630 false)⟩))
(.branch 13847
(.leaf ⟨13828,19,(.group 10 444 false)⟩)
(.leaf ⟨13847,20,(.group 10 543 false)⟩)))
(.branch 13909
(.branch 13888
(.leaf ⟨13867,21,(.group 10 629 false)⟩)
(.leaf ⟨13888,21,(.group 10 628 false)⟩))
(.branch 13931
(.leaf ⟨13909,22,(.group 10 745 false)⟩)
(.leaf ⟨13931,19,(.group 10 443 false)⟩))))))
(.branch 14271
(.branch 14111
(.branch 14025
(.branch 13987
(.branch 13972
(.leaf ⟨13950,22,(.group 10 744 false)⟩)
(.leaf ⟨13972,15,(.group 10 193 false)⟩))
(.branch 14008
(.leaf ⟨13987,21,(.group 10 627 false)⟩)
(.leaf ⟨14008,17,(.group 10 292 false)⟩)))
(.branch 14068
(.branch 14045
(.leaf ⟨14025,20,(.group 10 542 false)⟩)
(.leaf ⟨14045,23,(.group 10 874 false)⟩))
(.branch 14088
(.leaf ⟨14068,20,(.group 10 541 false)⟩)
(.leaf ⟨14088,23,(.group 10 873 false)⟩))))
(.branch 14193
(.branch 14148
(.branch 14126
(.leaf ⟨14111,15,(.group 10 192 false)⟩)
(.leaf ⟨14126,22,(.group 10 743 false)⟩))
(.branch 14171
(.leaf ⟨14148,23,(.group 10 872 false)⟩)
(.leaf ⟨14171,22,(.group 10 742 false)⟩)))
(.branch 14239
(.branch 14216
(.leaf ⟨14193,23,(.group 10 871 false)⟩)
(.leaf ⟨14216,23,(.group 10 870 false)⟩))
(.branch 14259
(.leaf ⟨14239,20,(.group 10 540 false)⟩)
(.leaf ⟨14259,12,(.group 10 88 false)⟩)))))
(.branch 14435
(.branch 14349
(.branch 14309
(.branch 14291
(.leaf ⟨14271,20,(.group 10 539 false)⟩)
(.leaf ⟨14291,18,(.group 10 371 false)⟩))
(.branch 14332
(.leaf ⟨14309,23,(.group 10 869 false)⟩)
(.leaf ⟨14332,17,(.group 10 291 false)⟩)))
(.branch 14389
(.branch 14370
(.leaf ⟨14349,21,(.group 10 626 false)⟩)
(.leaf ⟨14370,19,(.group 10 442 false)⟩))
(.branch 14412
(.leaf ⟨14389,23,(.group 10 868 false)⟩)
(.leaf ⟨14412,23,(.group 10 867 false)⟩))))
(.branch 14506
(.branch 14474
(.branch 14457
(.leaf ⟨14435,22,(.group 10 741 false)⟩)
(.leaf ⟨14457,17,(.group 10 290 false)⟩))
(.branch 14485
(.leaf ⟨14474,11,(.group 8 95 false)⟩)
(.leaf ⟨14485,21,(.group 10 625 false)⟩)))
(.branch 14538
(.branch 14526
(.leaf ⟨14506,20,(.group 10 538 false)⟩)
(.leaf ⟨14526,12,(.group 10 87 false)⟩))
(.branch 14549
(.leaf ⟨14538,11,(.group 8 94 false)⟩)
(.leaf ⟨14549,17,(.group 10 289 false)⟩)))))))

theorem tree11_checked : tree11.check 13286 14566 = true := by decide +kernel

def tree12 : Tree := (.branch 15209
(.branch 14890
(.branch 14722
(.branch 14643
(.branch 14610
(.branch 14589
(.leaf ⟨14566,23,(.group 10 866 false)⟩)
(.leaf ⟨14589,21,(.group 10 624 false)⟩))
(.branch 14625
(.leaf ⟨14610,15,(.group 10 191 false)⟩)
(.leaf ⟨14625,18,(.group 10 370 false)⟩)))
(.branch 14680
(.branch 14665
(.leaf ⟨14643,22,(.group 10 740 false)⟩)
(.leaf ⟨14665,15,(.group 10 190 false)⟩))
(.branch 14703
(.leaf ⟨14680,23,(.group 10 865 false)⟩)
(.leaf ⟨14703,19,(.group 10 441 false)⟩))))
(.branch 14803
(.branch 14764
(.branch 14743
(.leaf ⟨14722,21,(.group 10 623 false)⟩)
(.leaf ⟨14743,21,(.group 10 622 false)⟩))
(.branch 14784
(.leaf ⟨14764,20,(.group 10 537 false)⟩)
(.leaf ⟨14784,19,(.group 10 440 false)⟩)))
(.branch 14848
(.branch 14825
(.leaf ⟨14803,22,(.group 10 739 false)⟩)
(.leaf ⟨14825,23,(.group 10 864 false)⟩))
(.branch 14871
(.leaf ⟨14848,23,(.group 10 863 false)⟩)
(.leaf ⟨14871,19,(.group 10 439 false)⟩)))))
(.branch 15048
(.branch 14968
(.branch 14925
(.branch 14904
(.leaf ⟨14890,14,(.group 10 150 false)⟩)
(.leaf ⟨14904,21,(.group 10 621 false)⟩))
(.branch 14947
(.leaf ⟨14925,22,(.group 10 738 false)⟩)
(.leaf ⟨14947,21,(.group 10 620 false)⟩)))
(.branch 15013
(.branch 14991
(.leaf ⟨14968,23,(.group 10 862 false)⟩)
(.leaf ⟨14991,22,(.group 10 737 false)⟩))
(.branch 15029
(.leaf ⟨15013,16,(.group 10 235 false)⟩)
(.leaf ⟨15029,19,(.group 10 438 false)⟩))))
(.branch 15128
(.branch 15090
(.branch 15070
(.leaf ⟨15048,22,(.group 10 736 false)⟩)
(.leaf ⟨15070,20,(.group 10 536 false)⟩))
(.branch 15109
(.leaf ⟨15090,19,(.group 10 437 false)⟩)
(.leaf ⟨15109,19,(.group 10 436 false)⟩)))
(.branch 15166
(.branch 15143
(.leaf ⟨15128,15,(.group 10 189 false)⟩)
(.leaf ⟨15143,23,(.group 10 861 false)⟩))
(.branch 15188
(.leaf ⟨15166,22,(.group 10 735 false)⟩)
(.leaf ⟨15188,21,(.group 10 619 false)⟩))))))
(.branch 15527
(.branch 15363
(.branch 15288
(.branch 15243
(.branch 15224
(.leaf ⟨15209,15,(.group 10 188 false)⟩)
(.leaf ⟨15224,19,(.group 10 435 false)⟩))
(.branch 15265
(.leaf ⟨15243,22,(.group 10 734 false)⟩)
(.leaf ⟨15265,23,(.group 10 860 false)⟩)))
(.branch 15324
(.branch 15303
(.leaf ⟨15288,15,(.group 10 187 false)⟩)
(.leaf ⟨15303,21,(.group 10 618 false)⟩))
(.branch 15342
(.leaf ⟨15324,18,(.group 10 369 false)⟩)
(.leaf ⟨15342,21,(.group 10 617 false)⟩))))
(.branch 15443
(.branch 15405
(.branch 15383
(.leaf ⟨15363,20,(.group 10 535 false)⟩)
(.leaf ⟨15383,22,(.group 10 733 false)⟩))
(.branch 15428
(.leaf ⟨15405,23,(.group 10 859 false)⟩)
(.leaf ⟨15428,15,(.group 10 186 false)⟩)))
(.branch 15482
(.branch 15463
(.leaf ⟨15443,20,(.group 10 534 false)⟩)
(.leaf ⟨15463,19,(.group 10 434 false)⟩))
(.branch 15504
(.leaf ⟨15482,22,(.group 10 732 false)⟩)
(.leaf ⟨15504,23,(.group 9 1023 false)⟩)))))
(.branch 15692
(.branch 15602
(.branch 15560
(.branch 15547
(.leaf ⟨15527,20,(.group 10 533 false)⟩)
(.leaf ⟨15547,13,(.group 10 116 false)⟩))
(.branch 15579
(.leaf ⟨15560,19,(.group 10 433 false)⟩)
(.leaf ⟨15579,23,(.group 9 1022 false)⟩)))
(.branch 15647
(.branch 15624
(.leaf ⟨15602,22,(.group 10 731 false)⟩)
(.leaf ⟨15624,23,(.group 9 1021 false)⟩))
(.branch 15670
(.leaf ⟨15647,23,(.group 9 1020 false)⟩)
(.leaf ⟨15670,22,(.group 10 730 false)⟩))))
(.branch 15779
(.branch 15734
(.branch 15711
(.leaf ⟨15692,19,(.group 10 432 false)⟩)
(.leaf ⟨15711,23,(.group 9 1019 false)⟩))
(.branch 15756
(.leaf ⟨15734,22,(.group 10 729 false)⟩)
(.leaf ⟨15756,23,(.group 9 1018 false)⟩)))
(.branch 15822
(.branch 15801
(.leaf ⟨15779,22,(.group 10 728 false)⟩)
(.leaf ⟨15801,21,(.group 10 616 false)⟩))
(.branch 15840
(.leaf ⟨15822,18,(.group 10 368 false)⟩)
(.leaf ⟨15840,16,(.group 10 234 false)⟩)))))))

theorem tree12_checked : tree12.check 14566 15856 = true := by decide +kernel

def tree13 : Tree := (.branch 16489
(.branch 16177
(.branch 16003
(.branch 15927
(.branch 15898
(.branch 15879
(.leaf ⟨15856,23,(.group 9 1017 false)⟩)
(.leaf ⟨15879,19,(.group 10 431 false)⟩))
(.branch 15920
(.leaf ⟨15898,22,(.group 10 727 false)⟩)
(.leaf ⟨15920,7,(.group 6 9 false)⟩)))
(.branch 15963
(.branch 15947
(.leaf ⟨15927,20,(.group 10 532 false)⟩)
(.leaf ⟨15947,16,(.group 10 233 false)⟩))
(.branch 15984
(.leaf ⟨15963,21,(.group 10 615 false)⟩)
(.leaf ⟨15984,19,(.group 10 430 false)⟩))))
(.branch 16088
(.branch 16048
(.branch 16025
(.leaf ⟨16003,22,(.group 10 726 false)⟩)
(.leaf ⟨16025,23,(.group 9 1016 false)⟩))
(.branch 16066
(.leaf ⟨16048,18,(.group 10 367 false)⟩)
(.leaf ⟨16066,22,(.group 10 725 false)⟩)))
(.branch 16134
(.branch 16111
(.leaf ⟨16088,23,(.group 9 1015 false)⟩)
(.leaf ⟨16111,23,(.group 9 1014 false)⟩))
(.branch 16154
(.leaf ⟨16134,20,(.group 10 531 false)⟩)
(.leaf ⟨16154,23,(.group 9 1013 false)⟩)))))
(.branch 16339
(.branch 16257
(.branch 16217
(.branch 16194
(.leaf ⟨16177,17,(.group 10 288 false)⟩)
(.leaf ⟨16194,23,(.group 9 1012 false)⟩))
(.branch 16235
(.leaf ⟨16217,18,(.group 10 366 false)⟩)
(.leaf ⟨16235,22,(.group 10 724 false)⟩)))
(.branch 16302
(.branch 16279
(.leaf ⟨16257,22,(.group 10 723 false)⟩)
(.leaf ⟨16279,23,(.group 9 1011 false)⟩))
(.branch 16319
(.leaf ⟨16302,17,(.group 10 287 false)⟩)
(.leaf ⟨16319,20,(.group 10 530 false)⟩))))
(.branch 16420
(.branch 16382
(.branch 16361
(.leaf ⟨16339,22,(.group 9 1004 false)⟩)
(.leaf ⟨16361,21,(.group 10 614 false)⟩))
(.branch 16401
(.leaf ⟨16382,19,(.group 10 429 false)⟩)
(.leaf ⟨16401,19,(.group 10 428 false)⟩)))
(.branch 16451
(.branch 16436
(.leaf ⟨16420,16,(.group 10 232 false)⟩)
(.leaf ⟨16436,15,(.group 10 185 false)⟩))
(.branch 16472
(.leaf ⟨16451,21,(.group 10 613 false)⟩)
(.leaf ⟨16472,17,(.group 10 286 false)⟩))))))
(.branch 16798
(.branch 16650
(.branch 16567
(.branch 16521
(.branch 16504
(.leaf ⟨16489,15,(.group 10 184 false)⟩)
(.leaf ⟨16504,17,(.group 10 285 false)⟩))
(.branch 16544
(.leaf ⟨16521,23,(.group 9 1010 false)⟩)
(.leaf ⟨16544,23,(.group 9 1009 false)⟩)))
(.branch 16605
(.branch 16582
(.leaf ⟨16567,15,(.group 10 183 false)⟩)
(.leaf ⟨16582,23,(.group 9 1008 false)⟩))
(.branch 16628
(.leaf ⟨16605,23,(.group 9 1007 false)⟩)
(.leaf ⟨16628,22,(.group 9 1003 false)⟩))))
(.branch 16724
(.branch 16690
(.branch 16669
(.leaf ⟨16650,19,(.group 10 427 false)⟩)
(.leaf ⟨16669,21,(.group 10 612 false)⟩))
(.branch 16708
(.leaf ⟨16690,18,(.group 10 365 false)⟩)
(.leaf ⟨16708,16,(.group 10 231 false)⟩)))
(.branch 16760
(.branch 16741
(.leaf ⟨16724,17,(.group 10 284 false)⟩)
(.leaf ⟨16741,19,(.group 10 426 false)⟩))
(.branch 16778
(.leaf ⟨16760,18,(.group 10 364 false)⟩)
(.leaf ⟨16778,20,(.group 10 529 false)⟩)))))
(.branch 16960
(.branch 16880
(.branch 16838
(.branch 16818
(.leaf ⟨16798,20,(.group 10 528 false)⟩)
(.leaf ⟨16818,20,(.group 8 718 false)⟩))
(.branch 16858
(.leaf ⟨16838,20,(.group 10 527 false)⟩)
(.leaf ⟨16858,22,(.group 9 1002 false)⟩)))
(.branch 16922
(.branch 16902
(.leaf ⟨16880,22,(.group 9 1001 false)⟩)
(.leaf ⟨16902,20,(.group 10 526 false)⟩))
(.branch 16942
(.leaf ⟨16922,20,(.group 10 525 false)⟩)
(.leaf ⟨16942,18,(.group 10 363 false)⟩))))
(.branch 17044
(.branch 17003
(.branch 16982
(.leaf ⟨16960,22,(.group 9 1000 false)⟩)
(.leaf ⟨16982,21,(.group 10 611 false)⟩))
(.branch 17022
(.leaf ⟨17003,19,(.group 10 425 false)⟩)
(.leaf ⟨17022,22,(.group 9 999 false)⟩)))
(.branch 17089
(.branch 17067
(.leaf ⟨17044,23,(.group 9 1006 false)⟩)
(.leaf ⟨17067,22,(.group 9 998 false)⟩))
(.branch 17110
(.leaf ⟨17089,21,(.group 10 610 false)⟩)
(.leaf ⟨17110,23,(.group 9 1005 false)⟩)))))))

theorem tree13_checked : tree13.check 15856 17133 = true := by decide +kernel

def tree14 : Tree := (.branch 17765
(.branch 17452
(.branch 17294
(.branch 17215
(.branch 17169
(.branch 17154
(.leaf ⟨17133,21,(.group 10 609 false)⟩)
(.leaf ⟨17154,15,(.group 10 182 false)⟩))
(.branch 17192
(.leaf ⟨17169,23,(.group 8 1023 false)⟩)
(.leaf ⟨17192,23,(.group 8 1022 false)⟩)))
(.branch 17248
(.branch 17229
(.leaf ⟨17215,14,(.group 10 149 false)⟩)
(.leaf ⟨17229,19,(.group 10 424 false)⟩))
(.branch 17271
(.leaf ⟨17248,23,(.group 8 1021 false)⟩)
(.leaf ⟨17271,23,(.group 8 1020 false)⟩))))
(.branch 17378
(.branch 17335
(.branch 17316
(.leaf ⟨17294,22,(.group 9 997 false)⟩)
(.leaf ⟨17316,19,(.group 10 423 false)⟩))
(.branch 17357
(.leaf ⟨17335,22,(.group 9 996 false)⟩)
(.leaf ⟨17357,21,(.group 10 608 false)⟩)))
(.branch 17421
(.branch 17400
(.leaf ⟨17378,22,(.group 9 995 false)⟩)
(.leaf ⟨17400,21,(.group 10 607 false)⟩))
(.branch 17438
(.leaf ⟨17421,17,(.group 10 283 false)⟩)
(.leaf ⟨17438,14,(.group 10 148 false)⟩)))))
(.branch 17615
(.branch 17530
(.branch 17492
(.branch 17475
(.leaf ⟨17452,23,(.group 8 1019 false)⟩)
(.leaf ⟨17475,17,(.group 10 282 false)⟩))
(.branch 17510
(.leaf ⟨17492,18,(.group 10 362 false)⟩)
(.leaf ⟨17510,20,(.group 10 524 false)⟩)))
(.branch 17574
(.branch 17553
(.leaf ⟨17530,23,(.group 8 1018 false)⟩)
(.leaf ⟨17553,21,(.group 10 606 false)⟩))
(.branch 17592
(.leaf ⟨17574,18,(.group 10 361 false)⟩)
(.leaf ⟨17592,23,(.group 8 1017 false)⟩))))
(.branch 17685
(.branch 17648
(.branch 17633
(.leaf ⟨17615,18,(.group 10 360 false)⟩)
(.leaf ⟨17633,15,(.group 10 181 false)⟩))
(.branch 17669
(.leaf ⟨17648,21,(.group 10 605 false)⟩)
(.leaf ⟨17669,16,(.group 10 230 false)⟩)))
(.branch 17726
(.branch 17704
(.leaf ⟨17685,19,(.group 10 422 false)⟩)
(.leaf ⟨17704,22,(.group 9 994 false)⟩))
(.branch 17747
(.leaf ⟨17726,21,(.group 10 604 false)⟩)
(.leaf ⟨17747,18,(.group 10 359 false)⟩))))))
(.branch 18090
(.branch 17925
(.branch 17848
(.branch 17804
(.branch 17784
(.leaf ⟨17765,19,(.group 10 421 false)⟩)
(.leaf ⟨17784,20,(.group 10 523 false)⟩))
(.branch 17825
(.leaf ⟨17804,21,(.group 10 603 false)⟩)
(.leaf ⟨17825,23,(.group 8 1016 false)⟩)))
(.branch 17887
(.branch 17871
(.leaf ⟨17848,23,(.group 7 995 false)⟩)
(.leaf ⟨17871,16,(.group 10 229 false)⟩))
(.branch 17906
(.leaf ⟨17887,19,(.group 10 420 false)⟩)
(.leaf ⟨17906,19,(.group 10 419 false)⟩))))
(.branch 18005
(.branch 17960
(.branch 17941
(.leaf ⟨17925,16,(.group 10 228 false)⟩)
(.leaf ⟨17941,19,(.group 10 418 false)⟩))
(.branch 17983
(.leaf ⟨17960,23,(.group 7 994 false)⟩)
(.leaf ⟨17983,22,(.group 9 993 false)⟩)))
(.branch 18048
(.branch 18025
(.leaf ⟨18005,20,(.group 10 522 false)⟩)
(.leaf ⟨18025,23,(.group 7 993 false)⟩))
(.branch 18067
(.leaf ⟨18048,19,(.group 10 417 false)⟩)
(.leaf ⟨18067,23,(.group 7 992 false)⟩)))))
(.branch 18252
(.branch 18165
(.branch 18127
(.branch 18109
(.leaf ⟨18090,19,(.group 10 416 false)⟩)
(.leaf ⟨18109,18,(.group 10 358 false)⟩))
(.branch 18145
(.leaf ⟨18127,18,(.group 10 357 false)⟩)
(.leaf ⟨18145,20,(.group 10 521 false)⟩)))
(.branch 18210
(.branch 18187
(.leaf ⟨18165,22,(.group 9 992 false)⟩)
(.leaf ⟨18187,23,(.group 7 991 false)⟩))
(.branch 18231
(.leaf ⟨18210,21,(.group 9 851 false)⟩)
(.leaf ⟨18231,21,(.group 9 850 false)⟩))))
(.branch 18336
(.branch 18297
(.branch 18274
(.leaf ⟨18252,22,(.group 9 991 false)⟩)
(.leaf ⟨18274,23,(.group 7 990 false)⟩))
(.branch 18319
(.leaf ⟨18297,22,(.group 9 990 false)⟩)
(.leaf ⟨18319,17,(.group 10 281 false)⟩)))
(.branch 18382
(.branch 18359
(.leaf ⟨18336,23,(.group 7 989 false)⟩)
(.leaf ⟨18359,23,(.group 7 988 false)⟩))
(.branch 18405
(.leaf ⟨18382,23,(.group 7 987 false)⟩)
(.leaf ⟨18405,21,(.group 9 849 false)⟩)))))))

theorem tree14_checked : tree14.check 17133 18426 = true := by decide +kernel

def tree15 : Tree := (.branch 19081
(.branch 18755
(.branch 18587
(.branch 18503
(.branch 18470
(.branch 18447
(.leaf ⟨18426,21,(.group 9 848 false)⟩)
(.leaf ⟨18447,23,(.group 7 986 false)⟩))
(.branch 18493
(.leaf ⟨18470,23,(.group 7 985 false)⟩)
(.leaf ⟨18493,10,(.group 10 44 false)⟩)))
(.branch 18543
(.branch 18526
(.leaf ⟨18503,23,(.group 7 984 false)⟩)
(.leaf ⟨18526,17,(.group 10 280 false)⟩))
(.branch 18566
(.leaf ⟨18543,23,(.group 7 983 false)⟩)
(.leaf ⟨18566,21,(.group 9 847 false)⟩))))
(.branch 18673
(.branch 18628
(.branch 18605
(.leaf ⟨18587,18,(.group 10 356 false)⟩)
(.leaf ⟨18605,23,(.group 7 982 false)⟩))
(.branch 18650
(.leaf ⟨18628,22,(.group 9 989 false)⟩)
(.leaf ⟨18650,23,(.group 7 981 false)⟩)))
(.branch 18711
(.branch 18690
(.leaf ⟨18673,17,(.group 10 279 false)⟩)
(.leaf ⟨18690,21,(.group 9 846 false)⟩))
(.branch 18734
(.leaf ⟨18711,23,(.group 7 980 false)⟩)
(.leaf ⟨18734,21,(.group 9 845 false)⟩)))))
(.branch 18914
(.branch 18838
(.branch 18796
(.branch 18775
(.leaf ⟨18755,20,(.group 10 520 false)⟩)
(.leaf ⟨18775,21,(.group 9 844 false)⟩))
(.branch 18818
(.leaf ⟨18796,22,(.group 9 988 false)⟩)
(.leaf ⟨18818,20,(.group 10 519 false)⟩)))
(.branch 18871
(.branch 18849
(.leaf ⟨18838,11,(.group 10 59 false)⟩)
(.leaf ⟨18849,22,(.group 9 987 false)⟩))
(.branch 18892
(.leaf ⟨18871,21,(.group 9 843 false)⟩)
(.leaf ⟨18892,22,(.group 9 986 false)⟩))))
(.branch 19000
(.branch 18954
(.branch 18931
(.leaf ⟨18914,17,(.group 10 278 false)⟩)
(.leaf ⟨18931,23,(.group 7 979 false)⟩))
(.branch 18977
(.leaf ⟨18954,23,(.group 7 978 false)⟩)
(.leaf ⟨18977,23,(.group 7 977 false)⟩)))
(.branch 19038
(.branch 19022
(.leaf ⟨19000,22,(.group 9 985 false)⟩)
(.leaf ⟨19022,16,(.group 10 227 false)⟩))
(.branch 19058
(.leaf ⟨19038,20,(.group 10 518 false)⟩)
(.leaf ⟨19058,23,(.group 7 976 false)⟩))))))
(.branch 19399
(.branch 19245
(.branch 19162
(.branch 19121
(.branch 19104
(.leaf ⟨19081,23,(.group 7 975 false)⟩)
(.leaf ⟨19104,17,(.group 10 277 false)⟩))
(.branch 19141
(.leaf ⟨19121,20,(.group 10 517 false)⟩)
(.leaf ⟨19141,21,(.group 9 842 false)⟩)))
(.branch 19204
(.branch 19182
(.leaf ⟨19162,20,(.group 10 516 false)⟩)
(.leaf ⟨19182,22,(.group 9 984 false)⟩))
(.branch 19222
(.leaf ⟨19204,18,(.group 10 355 false)⟩)
(.leaf ⟨19222,23,(.group 7 974 false)⟩))))
(.branch 19325
(.branch 19282
(.branch 19263
(.leaf ⟨19245,18,(.group 10 354 false)⟩)
(.leaf ⟨19263,19,(.group 10 415 false)⟩))
(.branch 19304
(.leaf ⟨19282,22,(.group 9 983 false)⟩)
(.leaf ⟨19304,21,(.group 9 841 false)⟩)))
(.branch 19358
(.branch 19338
(.leaf ⟨19325,13,(.group 10 115 false)⟩)
(.leaf ⟨19338,20,(.group 10 515 false)⟩))
(.branch 19376
(.leaf ⟨19358,18,(.group 10 353 false)⟩)
(.leaf ⟨19376,23,(.group 7 973 false)⟩)))))
(.branch 19565
(.branch 19483
(.branch 19445
(.branch 19422
(.leaf ⟨19399,23,(.group 7 972 false)⟩)
(.leaf ⟨19422,23,(.group 7 971 false)⟩))
(.branch 19467
(.leaf ⟨19445,22,(.group 9 982 false)⟩)
(.leaf ⟨19467,16,(.group 10 226 false)⟩)))
(.branch 19523
(.branch 19501
(.leaf ⟨19483,18,(.group 10 352 false)⟩)
(.leaf ⟨19501,22,(.group 9 981 false)⟩))
(.branch 19542
(.leaf ⟨19523,19,(.group 10 414 false)⟩)
(.leaf ⟨19542,23,(.group 7 970 false)⟩))))
(.branch 19629
(.branch 19595
(.branch 19582
(.leaf ⟨19565,17,(.group 10 276 false)⟩)
(.leaf ⟨19582,13,(.group 8 158 false)⟩))
(.branch 19616
(.leaf ⟨19595,21,(.group 9 840 false)⟩)
(.leaf ⟨19616,13,(.group 10 114 false)⟩)))
(.branch 19671
(.branch 19650
(.leaf ⟨19629,21,(.group 9 839 false)⟩)
(.leaf ⟨19650,21,(.group 9 838 false)⟩))
(.branch 19693
(.leaf ⟨19671,22,(.group 9 980 false)⟩)
(.leaf ⟨19693,19,(.group 10 413 false)⟩)))))))

theorem tree15_checked : tree15.check 18426 19712 = true := by decide +kernel

def tree16 : Tree := (.branch 20341
(.branch 20027
(.branch 19863
(.branch 19779
(.branch 19754
(.branch 19733
(.leaf ⟨19712,21,(.group 9 837 false)⟩)
(.leaf ⟨19733,21,(.group 9 836 false)⟩))
(.branch 19767
(.leaf ⟨19754,13,(.group 10 113 false)⟩)
(.leaf ⟨19767,12,(.group 10 86 false)⟩)))
(.branch 19820
(.branch 19799
(.leaf ⟨19779,20,(.group 10 514 false)⟩)
(.leaf ⟨19799,21,(.group 9 835 false)⟩))
(.branch 19843
(.leaf ⟨19820,23,(.group 7 969 false)⟩)
(.leaf ⟨19843,20,(.group 10 513 false)⟩))))
(.branch 19948
(.branch 19903
(.branch 19885
(.leaf ⟨19863,22,(.group 9 979 false)⟩)
(.leaf ⟨19885,18,(.group 10 351 false)⟩))
(.branch 19925
(.leaf ⟨19903,22,(.group 9 978 false)⟩)
(.leaf ⟨19925,23,(.group 7 968 false)⟩)))
(.branch 19987
(.branch 19971
(.leaf ⟨19948,23,(.group 7 967 false)⟩)
(.leaf ⟨19971,16,(.group 10 225 false)⟩))
(.branch 20007
(.leaf ⟨19987,20,(.group 10 512 false)⟩)
(.leaf ⟨20007,20,(.group 10 511 false)⟩)))))
(.branch 20194
(.branch 20114
(.branch 20069
(.branch 20048
(.leaf ⟨20027,21,(.group 9 834 false)⟩)
(.leaf ⟨20048,21,(.group 9 833 false)⟩))
(.branch 20091
(.leaf ⟨20069,22,(.group 9 977 false)⟩)
(.leaf ⟨20091,23,(.group 7 966 false)⟩)))
(.branch 20156
(.branch 20137
(.leaf ⟨20114,23,(.group 7 965 false)⟩)
(.leaf ⟨20137,19,(.group 10 412 false)⟩))
(.branch 20173
(.leaf ⟨20156,17,(.group 10 275 false)⟩)
(.leaf ⟨20173,21,(.group 9 832 false)⟩))))
(.branch 20269
(.branch 20231
(.branch 20215
(.leaf ⟨20194,21,(.group 9 831 false)⟩)
(.leaf ⟨20215,16,(.group 10 224 false)⟩))
(.branch 20251
(.leaf ⟨20231,20,(.group 10 510 false)⟩)
(.leaf ⟨20251,18,(.group 10 350 false)⟩)))
(.branch 20304
(.branch 20284
(.leaf ⟨20269,15,(.group 10 180 false)⟩)
(.leaf ⟨20284,20,(.group 10 509 false)⟩))
(.branch 20325
(.leaf ⟨20304,21,(.group 9 830 false)⟩)
(.leaf ⟨20325,16,(.group 10 223 false)⟩))))))
(.branch 20659
(.branch 20498
(.branch 20422
(.branch 20381
(.branch 20360
(.leaf ⟨20341,19,(.group 8 598 false)⟩)
(.leaf ⟨20360,21,(.group 9 829 false)⟩))
(.branch 20403
(.leaf ⟨20381,22,(.group 9 976 false)⟩)
(.leaf ⟨20403,19,(.group 10 411 false)⟩)))
(.branch 20458
(.branch 20436
(.leaf ⟨20422,14,(.group 10 147 false)⟩)
(.leaf ⟨20436,22,(.group 9 975 false)⟩))
(.branch 20478
(.leaf ⟨20458,20,(.group 10 508 false)⟩)
(.leaf ⟨20478,20,(.group 10 507 false)⟩))))
(.branch 20574
(.branch 20539
(.branch 20516
(.leaf ⟨20498,18,(.group 10 349 false)⟩)
(.leaf ⟨20516,23,(.group 7 964 false)⟩))
(.branch 20554
(.leaf ⟨20539,15,(.group 10 179 false)⟩)
(.leaf ⟨20554,20,(.group 10 506 false)⟩)))
(.branch 20615
(.branch 20593
(.leaf ⟨20574,19,(.group 10 410 false)⟩)
(.leaf ⟨20593,22,(.group 9 974 false)⟩))
(.branch 20638
(.leaf ⟨20615,23,(.group 7 963 false)⟩)
(.leaf ⟨20638,21,(.group 9 828 false)⟩)))))
(.branch 20821
(.branch 20740
(.branch 20699
(.branch 20678
(.leaf ⟨20659,19,(.group 10 409 false)⟩)
(.leaf ⟨20678,21,(.group 9 827 false)⟩))
(.branch 20722
(.leaf ⟨20699,23,(.group 7 962 false)⟩)
(.leaf ⟨20722,18,(.group 10 348 false)⟩)))
(.branch 20785
(.branch 20763
(.leaf ⟨20740,23,(.group 7 961 false)⟩)
(.leaf ⟨20763,22,(.group 9 973 false)⟩))
(.branch 20802
(.leaf ⟨20785,17,(.group 10 274 false)⟩)
(.leaf ⟨20802,19,(.group 10 408 false)⟩))))
(.branch 20908
(.branch 20862
(.branch 20841
(.leaf ⟨20821,20,(.group 10 505 false)⟩)
(.leaf ⟨20841,21,(.group 9 826 false)⟩))
(.branch 20885
(.leaf ⟨20862,23,(.group 7 960 false)⟩)
(.leaf ⟨20885,23,(.group 7 959 false)⟩)))
(.branch 20945
(.branch 20931
(.leaf ⟨20908,23,(.group 7 958 false)⟩)
(.leaf ⟨20931,14,(.group 10 146 false)⟩))
(.branch 20968
(.leaf ⟨20945,23,(.group 7 957 false)⟩)
(.leaf ⟨20968,23,(.group 7 956 false)⟩)))))))

theorem tree16_checked : tree16.check 19712 20991 = true := by decide +kernel

def tree17 : Tree := (.branch 21638
(.branch 21315
(.branch 21157
(.branch 21068
(.branch 21029
(.branch 21007
(.leaf ⟨20991,16,(.group 10 222 false)⟩)
(.leaf ⟨21007,22,(.group 9 972 false)⟩))
(.branch 21049
(.leaf ⟨21029,20,(.group 10 504 false)⟩)
(.leaf ⟨21049,19,(.group 10 407 false)⟩)))
(.branch 21112
(.branch 21090
(.leaf ⟨21068,22,(.group 9 971 false)⟩)
(.leaf ⟨21090,22,(.group 9 970 false)⟩))
(.branch 21135
(.leaf ⟨21112,23,(.group 7 955 false)⟩)
(.leaf ⟨21135,22,(.group 9 969 false)⟩))))
(.branch 21232
(.branch 21194
(.branch 21175
(.leaf ⟨21157,18,(.group 10 347 false)⟩)
(.leaf ⟨21175,19,(.group 9 595 false)⟩))
(.branch 21212
(.leaf ⟨21194,18,(.group 10 346 false)⟩)
(.leaf ⟨21212,20,(.group 10 503 false)⟩)))
(.branch 21274
(.branch 21251
(.leaf ⟨21232,19,(.group 9 594 false)⟩)
(.leaf ⟨21251,23,(.group 7 954 false)⟩))
(.branch 21295
(.leaf ⟨21274,21,(.group 9 825 false)⟩)
(.leaf ⟨21295,20,(.group 10 502 false)⟩)))))
(.branch 21470
(.branch 21387
(.branch 21349
(.branch 21334
(.leaf ⟨21315,19,(.group 9 593 false)⟩)
(.leaf ⟨21334,15,(.group 10 178 false)⟩))
(.branch 21370
(.leaf ⟨21349,21,(.group 8 864 false)⟩)
(.leaf ⟨21370,17,(.group 10 273 false)⟩)))
(.branch 21430
(.branch 21408
(.leaf ⟨21387,21,(.group 9 824 false)⟩)
(.leaf ⟨21408,22,(.group 9 968 false)⟩))
(.branch 21451
(.leaf ⟨21430,21,(.group 9 823 false)⟩)
(.leaf ⟨21451,19,(.group 9 592 false)⟩))))
(.branch 21552
(.branch 21508
(.branch 21493
(.leaf ⟨21470,23,(.group 7 953 false)⟩)
(.leaf ⟨21493,15,(.group 10 177 false)⟩))
(.branch 21531
(.leaf ⟨21508,23,(.group 7 952 false)⟩)
(.leaf ⟨21531,21,(.group 9 822 false)⟩)))
(.branch 21593
(.branch 21570
(.leaf ⟨21552,18,(.group 10 345 false)⟩)
(.leaf ⟨21570,23,(.group 7 951 false)⟩))
(.branch 21615
(.leaf ⟨21593,22,(.group 9 967 false)⟩)
(.leaf ⟨21615,23,(.group 7 950 false)⟩))))))
(.branch 21967
(.branch 21800
(.branch 21719
(.branch 21679
(.branch 21659
(.leaf ⟨21638,21,(.group 9 821 false)⟩)
(.leaf ⟨21659,20,(.group 10 501 false)⟩))
(.branch 21696
(.leaf ⟨21679,17,(.group 10 272 false)⟩)
(.leaf ⟨21696,23,(.group 7 949 false)⟩)))
(.branch 21759
(.branch 21738
(.leaf ⟨21719,19,(.group 9 591 false)⟩)
(.leaf ⟨21738,21,(.group 9 820 false)⟩))
(.branch 21778
(.leaf ⟨21759,19,(.group 9 590 false)⟩)
(.leaf ⟨21778,22,(.group 9 966 false)⟩))))
(.branch 21883
(.branch 21843
(.branch 21820
(.leaf ⟨21800,20,(.group 10 500 false)⟩)
(.leaf ⟨21820,23,(.group 7 948 false)⟩))
(.branch 21862
(.leaf ⟨21843,19,(.group 9 589 false)⟩)
(.leaf ⟨21862,21,(.group 9 819 false)⟩)))
(.branch 21926
(.branch 21905
(.leaf ⟨21883,22,(.group 9 965 false)⟩)
(.leaf ⟨21905,21,(.group 9 818 false)⟩))
(.branch 21945
(.leaf ⟨21926,19,(.group 9 588 false)⟩)
(.leaf ⟨21945,22,(.group 9 964 false)⟩)))))
(.branch 22136
(.branch 22051
(.branch 22011
(.branch 21990
(.leaf ⟨21967,23,(.group 7 947 false)⟩)
(.leaf ⟨21990,21,(.group 9 817 false)⟩))
(.branch 22032
(.leaf ⟨22011,21,(.group 9 816 false)⟩)
(.leaf ⟨22032,19,(.group 9 587 false)⟩)))
(.branch 22094
(.branch 22072
(.leaf ⟨22051,21,(.group 9 815 false)⟩)
(.leaf ⟨22072,22,(.group 9 963 false)⟩))
(.branch 22114
(.leaf ⟨22094,20,(.group 10 499 false)⟩)
(.leaf ⟨22114,22,(.group 9 962 false)⟩))))
(.branch 22207
(.branch 22178
(.branch 22159
(.leaf ⟨22136,23,(.group 7 946 false)⟩)
(.leaf ⟨22159,19,(.group 9 586 false)⟩))
(.branch 22193
(.leaf ⟨22178,15,(.group 10 176 false)⟩)
(.leaf ⟨22193,14,(.group 10 145 false)⟩)))
(.branch 22250
(.branch 22227
(.leaf ⟨22207,20,(.group 10 498 false)⟩)
(.leaf ⟨22227,23,(.group 7 945 false)⟩))
(.branch 22272
(.leaf ⟨22250,22,(.group 9 961 false)⟩)
(.leaf ⟨22272,23,(.group 7 944 false)⟩)))))))

theorem tree17_checked : tree17.check 20991 22295 = true := by decide +kernel

def tree18 : Tree := (.branch 22935
(.branch 22607
(.branch 22450
(.branch 22365
(.branch 22323
(.branch 22307
(.leaf ⟨22295,12,(.group 10 85 false)⟩)
(.leaf ⟨22307,16,(.group 10 221 false)⟩))
(.branch 22346
(.leaf ⟨22323,23,(.group 7 943 false)⟩)
(.leaf ⟨22346,19,(.group 9 585 false)⟩)))
(.branch 22409
(.branch 22387
(.leaf ⟨22365,22,(.group 9 960 false)⟩)
(.leaf ⟨22387,22,(.group 9 959 false)⟩))
(.branch 22427
(.leaf ⟨22409,18,(.group 10 344 false)⟩)
(.leaf ⟨22427,23,(.group 7 942 false)⟩))))
(.branch 22526
(.branch 22484
(.branch 22473
(.leaf ⟨22450,23,(.group 7 941 false)⟩)
(.leaf ⟨22473,11,(.group 10 58 false)⟩))
(.branch 22507
(.leaf ⟨22484,23,(.group 7 940 false)⟩)
(.leaf ⟨22507,19,(.group 9 584 false)⟩)))
(.branch 22564
(.branch 22542
(.leaf ⟨22526,16,(.group 10 220 false)⟩)
(.leaf ⟨22542,22,(.group 9 958 false)⟩))
(.branch 22585
(.leaf ⟨22564,21,(.group 9 814 false)⟩)
(.leaf ⟨22585,22,(.group 9 957 false)⟩)))))
(.branch 22774
(.branch 22692
(.branch 22649
(.branch 22627
(.leaf ⟨22607,20,(.group 9 715 false)⟩)
(.leaf ⟨22627,22,(.group 9 956 false)⟩))
(.branch 22672
(.leaf ⟨22649,23,(.group 7 939 false)⟩)
(.leaf ⟨22672,20,(.group 9 714 false)⟩)))
(.branch 22732
(.branch 22711
(.leaf ⟨22692,19,(.group 9 583 false)⟩)
(.leaf ⟨22711,21,(.group 9 813 false)⟩))
(.branch 22754
(.leaf ⟨22732,22,(.group 9 955 false)⟩)
(.leaf ⟨22754,20,(.group 9 713 false)⟩))))
(.branch 22855
(.branch 22815
(.branch 22794
(.leaf ⟨22774,20,(.group 9 712 false)⟩)
(.leaf ⟨22794,21,(.group 9 812 false)⟩))
(.branch 22838
(.leaf ⟨22815,23,(.group 7 938 false)⟩)
(.leaf ⟨22838,17,(.group 10 271 false)⟩)))
(.branch 22891
(.branch 22873
(.leaf ⟨22855,18,(.group 10 343 false)⟩)
(.leaf ⟨22873,18,(.group 10 342 false)⟩))
(.branch 22914
(.leaf ⟨22891,23,(.group 7 937 false)⟩)
(.leaf ⟨22914,21,(.group 9 811 false)⟩))))))
(.branch 23266
(.branch 23100
(.branch 23018
(.branch 22977
(.branch 22957
(.leaf ⟨22935,22,(.group 9 954 false)⟩)
(.leaf ⟨22957,20,(.group 9 711 false)⟩))
(.branch 22999
(.leaf ⟨22977,22,(.group 9 953 false)⟩)
(.leaf ⟨22999,19,(.group 9 582 false)⟩)))
(.branch 23063
(.branch 23040
(.leaf ⟨23018,22,(.group 9 952 false)⟩)
(.leaf ⟨23040,23,(.group 7 936 false)⟩))
(.branch 23083
(.leaf ⟨23063,20,(.group 9 710 false)⟩)
(.leaf ⟨23083,17,(.group 10 270 false)⟩))))
(.branch 23181
(.branch 23139
(.branch 23123
(.leaf ⟨23100,23,(.group 7 935 false)⟩)
(.leaf ⟨23123,16,(.group 10 219 false)⟩))
(.branch 23162
(.leaf ⟨23139,23,(.group 7 934 false)⟩)
(.leaf ⟨23162,19,(.group 9 581 false)⟩)))
(.branch 23222
(.branch 23202
(.leaf ⟨23181,21,(.group 9 810 false)⟩)
(.leaf ⟨23202,20,(.group 9 709 false)⟩))
(.branch 23244
(.leaf ⟨23222,22,(.group 9 951 false)⟩)
(.leaf ⟨23244,22,(.group 9 950 false)⟩)))))
(.branch 23428
(.branch 23347
(.branch 23304
(.branch 23285
(.leaf ⟨23266,19,(.group 9 580 false)⟩)
(.leaf ⟨23285,19,(.group 9 579 false)⟩))
(.branch 23327
(.leaf ⟨23304,23,(.group 7 933 false)⟩)
(.leaf ⟨23327,20,(.group 9 708 false)⟩)))
(.branch 23386
(.branch 23368
(.leaf ⟨23347,21,(.group 9 809 false)⟩)
(.leaf ⟨23368,18,(.group 10 341 false)⟩))
(.branch 23406
(.leaf ⟨23386,20,(.group 9 707 false)⟩)
(.leaf ⟨23406,22,(.group 9 949 false)⟩))))
(.branch 23511
(.branch 23471
(.branch 23448
(.leaf ⟨23428,20,(.group 9 706 false)⟩)
(.leaf ⟨23448,23,(.group 7 932 false)⟩))
(.branch 23489
(.leaf ⟨23471,18,(.group 10 340 false)⟩)
(.leaf ⟨23489,22,(.group 9 948 false)⟩)))
(.branch 23550
(.branch 23529
(.leaf ⟨23511,18,(.group 10 339 false)⟩)
(.leaf ⟨23529,21,(.group 9 808 false)⟩))
(.branch 23569
(.leaf ⟨23550,19,(.group 9 578 false)⟩)
(.leaf ⟨23569,19,(.group 9 577 false)⟩)))))))

theorem tree18_checked : tree18.check 22295 23588 = true := by decide +kernel

def tree19 : Tree := (.branch 24232
(.branch 23914
(.branch 23766
(.branch 23680
(.branch 23634
(.branch 23611
(.leaf ⟨23588,23,(.group 7 931 false)⟩)
(.leaf ⟨23611,23,(.group 7 930 false)⟩))
(.branch 23657
(.leaf ⟨23634,23,(.group 7 929 false)⟩)
(.leaf ⟨23657,23,(.group 7 928 false)⟩)))
(.branch 23725
(.branch 23702
(.leaf ⟨23680,22,(.group 9 947 false)⟩)
(.leaf ⟨23702,23,(.group 7 927 false)⟩))
(.branch 23744
(.leaf ⟨23725,19,(.group 9 576 false)⟩)
(.leaf ⟨23744,22,(.group 9 946 false)⟩))))
(.branch 23841
(.branch 23801
(.branch 23781
(.leaf ⟨23766,15,(.group 10 175 false)⟩)
(.leaf ⟨23781,20,(.group 9 705 false)⟩))
(.branch 23820
(.leaf ⟨23801,19,(.group 9 575 false)⟩)
(.leaf ⟨23820,21,(.group 9 807 false)⟩)))
(.branch 23880
(.branch 23862
(.leaf ⟨23841,21,(.group 9 806 false)⟩)
(.leaf ⟨23862,18,(.group 10 338 false)⟩))
(.branch 23895
(.leaf ⟨23880,15,(.group 8 259 false)⟩)
(.leaf ⟨23895,19,(.group 9 574 false)⟩)))))
(.branch 24077
(.branch 23991
(.branch 23953
(.branch 23935
(.leaf ⟨23914,21,(.group 9 805 false)⟩)
(.leaf ⟨23935,18,(.group 10 337 false)⟩))
(.branch 23974
(.leaf ⟨23953,21,(.group 9 804 false)⟩)
(.leaf ⟨23974,17,(.group 10 269 false)⟩)))
(.branch 24031
(.branch 24008
(.leaf ⟨23991,17,(.group 10 268 false)⟩)
(.leaf ⟨24008,23,(.group 7 926 false)⟩))
(.branch 24054
(.leaf ⟨24031,23,(.group 7 925 false)⟩)
(.leaf ⟨24054,23,(.group 7 924 false)⟩))))
(.branch 24156
(.branch 24119
(.branch 24098
(.leaf ⟨24077,21,(.group 9 803 false)⟩)
(.leaf ⟨24098,21,(.group 9 802 false)⟩))
(.branch 24138
(.leaf ⟨24119,19,(.group 9 573 false)⟩)
(.leaf ⟨24138,18,(.group 10 336 false)⟩)))
(.branch 24195
(.branch 24177
(.leaf ⟨24156,21,(.group 9 801 false)⟩)
(.leaf ⟨24177,18,(.group 10 335 false)⟩))
(.branch 24210
(.leaf ⟨24195,15,(.group 10 174 false)⟩)
(.leaf ⟨24210,22,(.group 9 945 false)⟩))))))
(.branch 24555
(.branch 24395
(.branch 24318
(.branch 24277
(.branch 24254
(.leaf ⟨24232,22,(.group 9 944 false)⟩)
(.leaf ⟨24254,23,(.group 7 923 false)⟩))
(.branch 24298
(.leaf ⟨24277,21,(.group 9 800 false)⟩)
(.leaf ⟨24298,20,(.group 9 704 false)⟩)))
(.branch 24355
(.branch 24333
(.leaf ⟨24318,15,(.group 10 173 false)⟩)
(.leaf ⟨24333,22,(.group 9 943 false)⟩))
(.branch 24374
(.leaf ⟨24355,19,(.group 9 572 false)⟩)
(.leaf ⟨24374,21,(.group 9 799 false)⟩))))
(.branch 24474
(.branch 24436
(.branch 24415
(.leaf ⟨24395,20,(.group 9 703 false)⟩)
(.leaf ⟨24415,21,(.group 9 798 false)⟩))
(.branch 24454
(.leaf ⟨24436,18,(.group 10 334 false)⟩)
(.leaf ⟨24454,20,(.group 9 702 false)⟩)))
(.branch 24515
(.branch 24494
(.leaf ⟨24474,20,(.group 9 701 false)⟩)
(.leaf ⟨24494,21,(.group 9 797 false)⟩))
(.branch 24535
(.leaf ⟨24515,20,(.group 9 700 false)⟩)
(.leaf ⟨24535,20,(.group 9 699 false)⟩)))))
(.branch 24725
(.branch 24637
(.branch 24596
(.branch 24575
(.leaf ⟨24555,20,(.group 9 698 false)⟩)
(.leaf ⟨24575,21,(.group 9 796 false)⟩))
(.branch 24614
(.leaf ⟨24596,18,(.group 10 333 false)⟩)
(.leaf ⟨24614,23,(.group 7 922 false)⟩)))
(.branch 24681
(.branch 24658
(.leaf ⟨24637,21,(.group 9 795 false)⟩)
(.leaf ⟨24658,23,(.group 7 921 false)⟩))
(.branch 24703
(.leaf ⟨24681,22,(.group 9 942 false)⟩)
(.leaf ⟨24703,22,(.group 9 941 false)⟩))))
(.branch 24800
(.branch 24762
(.branch 24740
(.leaf ⟨24725,15,(.group 10 172 false)⟩)
(.leaf ⟨24740,22,(.group 9 940 false)⟩))
(.branch 24784
(.leaf ⟨24762,22,(.group 9 939 false)⟩)
(.leaf ⟨24784,16,(.group 10 218 false)⟩)))
(.branch 24841
(.branch 24821
(.leaf ⟨24800,21,(.group 9 794 false)⟩)
(.leaf ⟨24821,20,(.group 9 697 false)⟩))
(.branch 24861
(.leaf ⟨24841,20,(.group 9 696 false)⟩)
(.leaf ⟨24861,21,(.group 9 793 false)⟩)))))))

theorem tree19_checked : tree19.check 23588 24882 = true := by decide +kernel

def tree20 : Tree := (.branch 25531
(.branch 25198
(.branch 25048
(.branch 24965
(.branch 24926
(.branch 24905
(.leaf ⟨24882,23,(.group 7 920 false)⟩)
(.leaf ⟨24905,21,(.group 9 792 false)⟩))
(.branch 24945
(.leaf ⟨24926,19,(.group 9 571 false)⟩)
(.leaf ⟨24945,20,(.group 9 695 false)⟩)))
(.branch 25006
(.branch 24987
(.leaf ⟨24965,22,(.group 9 938 false)⟩)
(.leaf ⟨24987,19,(.group 9 570 false)⟩))
(.branch 25027
(.leaf ⟨25006,21,(.group 9 791 false)⟩)
(.leaf ⟨25027,21,(.group 9 790 false)⟩))))
(.branch 25127
(.branch 25086
(.branch 25068
(.leaf ⟨25048,20,(.group 9 694 false)⟩)
(.leaf ⟨25068,18,(.group 10 332 false)⟩))
(.branch 25106
(.leaf ⟨25086,20,(.group 9 693 false)⟩)
(.leaf ⟨25106,21,(.group 9 789 false)⟩)))
(.branch 25157
(.branch 25138
(.leaf ⟨25127,11,(.group 10 57 false)⟩)
(.leaf ⟨25138,19,(.group 9 569 false)⟩))
(.branch 25180
(.leaf ⟨25157,23,(.group 7 919 false)⟩)
(.leaf ⟨25180,18,(.group 10 331 false)⟩)))))
(.branch 25367
(.branch 25281
(.branch 25244
(.branch 25221
(.leaf ⟨25198,23,(.group 7 918 false)⟩)
(.leaf ⟨25221,23,(.group 7 917 false)⟩))
(.branch 25263
(.leaf ⟨25244,19,(.group 9 568 false)⟩)
(.leaf ⟨25263,18,(.group 10 330 false)⟩)))
(.branch 25323
(.branch 25301
(.leaf ⟨25281,20,(.group 9 692 false)⟩)
(.leaf ⟨25301,22,(.group 9 937 false)⟩))
(.branch 25345
(.leaf ⟨25323,22,(.group 9 936 false)⟩)
(.leaf ⟨25345,22,(.group 9 935 false)⟩))))
(.branch 25450
(.branch 25408
(.branch 25387
(.leaf ⟨25367,20,(.group 9 691 false)⟩)
(.leaf ⟨25387,21,(.group 9 788 false)⟩))
(.branch 25428
(.leaf ⟨25408,20,(.group 9 690 false)⟩)
(.leaf ⟨25428,22,(.group 9 934 false)⟩)))
(.branch 25493
(.branch 25472
(.leaf ⟨25450,22,(.group 9 933 false)⟩)
(.leaf ⟨25472,21,(.group 9 787 false)⟩))
(.branch 25515
(.leaf ⟨25493,22,(.group 9 932 false)⟩)
(.leaf ⟨25515,16,(.group 10 217 false)⟩))))))
(.branch 25839
(.branch 25679
(.branch 25606
(.branch 25568
(.branch 25552
(.leaf ⟨25531,21,(.group 9 786 false)⟩)
(.leaf ⟨25552,16,(.group 10 216 false)⟩))
(.branch 25585
(.leaf ⟨25568,17,(.group 10 267 false)⟩)
(.leaf ⟨25585,21,(.group 9 785 false)⟩)))
(.branch 25644
(.branch 25621
(.leaf ⟨25606,15,(.group 10 171 false)⟩)
(.leaf ⟨25621,23,(.group 7 916 false)⟩))
(.branch 25664
(.leaf ⟨25644,20,(.group 9 689 false)⟩)
(.leaf ⟨25664,15,(.group 10 170 false)⟩))))
(.branch 25761
(.branch 25716
(.branch 25699
(.leaf ⟨25679,20,(.group 9 688 false)⟩)
(.leaf ⟨25699,17,(.group 10 266 false)⟩))
(.branch 25738
(.leaf ⟨25716,22,(.group 9 931 false)⟩)
(.leaf ⟨25738,23,(.group 7 915 false)⟩)))
(.branch 25804
(.branch 25784
(.leaf ⟨25761,23,(.group 7 914 false)⟩)
(.leaf ⟨25784,20,(.group 9 687 false)⟩))
(.branch 25821
(.leaf ⟨25804,17,(.group 10 265 false)⟩)
(.leaf ⟨25821,18,(.group 10 329 false)⟩)))))
(.branch 26005
(.branch 25922
(.branch 25880
(.branch 25859
(.leaf ⟨25839,20,(.group 9 686 false)⟩)
(.leaf ⟨25859,21,(.group 9 784 false)⟩))
(.branch 25899
(.leaf ⟨25880,19,(.group 9 567 false)⟩)
(.leaf ⟨25899,23,(.group 7 913 false)⟩)))
(.branch 25960
(.branch 25944
(.leaf ⟨25922,22,(.group 9 930 false)⟩)
(.leaf ⟨25944,16,(.group 10 215 false)⟩))
(.branch 25982
(.leaf ⟨25960,22,(.group 9 929 false)⟩)
(.leaf ⟨25982,23,(.group 7 912 false)⟩))))
(.branch 26084
(.branch 26044
(.branch 26026
(.leaf ⟨26005,21,(.group 9 783 false)⟩)
(.leaf ⟨26026,18,(.group 9 490 false)⟩))
(.branch 26063
(.leaf ⟨26044,19,(.group 9 566 false)⟩)
(.leaf ⟨26063,21,(.group 9 782 false)⟩)))
(.branch 26120
(.branch 26105
(.leaf ⟨26084,21,(.group 9 781 false)⟩)
(.leaf ⟨26105,15,(.group 10 169 false)⟩))
(.branch 26139
(.leaf ⟨26120,19,(.group 9 565 false)⟩)
(.leaf ⟨26139,23,(.group 7 911 false)⟩)))))))

theorem tree20_checked : tree20.check 24882 26162 = true := by decide +kernel

def tree21 : Tree := (.branch 26824
(.branch 26488
(.branch 26320
(.branch 26243
(.branch 26207
(.branch 26185
(.leaf ⟨26162,23,(.group 7 910 false)⟩)
(.leaf ⟨26185,22,(.group 9 928 false)⟩))
(.branch 26224
(.leaf ⟨26207,17,(.group 10 264 false)⟩)
(.leaf ⟨26224,19,(.group 9 564 false)⟩)))
(.branch 26283
(.branch 26261
(.leaf ⟨26243,18,(.group 9 489 false)⟩)
(.leaf ⟨26261,22,(.group 9 927 false)⟩))
(.branch 26301
(.leaf ⟨26283,18,(.group 9 488 false)⟩)
(.leaf ⟨26301,19,(.group 9 563 false)⟩))))
(.branch 26408
(.branch 26365
(.branch 26342
(.leaf ⟨26320,22,(.group 9 926 false)⟩)
(.leaf ⟨26342,23,(.group 7 909 false)⟩))
(.branch 26386
(.leaf ⟨26365,21,(.group 9 780 false)⟩)
(.leaf ⟨26386,22,(.group 9 925 false)⟩)))
(.branch 26449
(.branch 26430
(.leaf ⟨26408,22,(.group 9 924 false)⟩)
(.leaf ⟨26430,19,(.group 9 562 false)⟩))
(.branch 26465
(.leaf ⟨26449,16,(.group 10 214 false)⟩)
(.leaf ⟨26465,23,(.group 7 908 false)⟩)))))
(.branch 26652
(.branch 26578
(.branch 26532
(.branch 26511
(.leaf ⟨26488,23,(.group 7 907 false)⟩)
(.leaf ⟨26511,21,(.group 9 779 false)⟩))
(.branch 26555
(.leaf ⟨26532,23,(.group 7 906 false)⟩)
(.leaf ⟨26555,23,(.group 7 905 false)⟩)))
(.branch 26609
(.branch 26590
(.leaf ⟨26578,12,(.group 10 84 false)⟩)
(.leaf ⟨26590,19,(.group 9 561 false)⟩))
(.branch 26631
(.leaf ⟨26609,22,(.group 9 923 false)⟩)
(.leaf ⟨26631,21,(.group 9 778 false)⟩))))
(.branch 26740
(.branch 26694
(.branch 26675
(.leaf ⟨26652,23,(.group 7 904 false)⟩)
(.leaf ⟨26675,19,(.group 9 560 false)⟩))
(.branch 26717
(.leaf ⟨26694,23,(.group 7 903 false)⟩)
(.leaf ⟨26717,23,(.group 7 902 false)⟩)))
(.branch 26784
(.branch 26762
(.leaf ⟨26740,22,(.group 9 922 false)⟩)
(.leaf ⟨26762,22,(.group 9 921 false)⟩))
(.branch 26804
(.leaf ⟨26784,20,(.group 9 685 false)⟩)
(.leaf ⟨26804,20,(.group 9 684 false)⟩))))))
(.branch 27160
(.branch 26988
(.branch 26904
(.branch 26865
(.branch 26845
(.leaf ⟨26824,21,(.group 9 777 false)⟩)
(.leaf ⟨26845,20,(.group 9 683 false)⟩))
(.branch 26885
(.leaf ⟨26865,20,(.group 9 682 false)⟩)
(.leaf ⟨26885,19,(.group 9 559 false)⟩)))
(.branch 26948
(.branch 26927
(.leaf ⟨26904,23,(.group 7 901 false)⟩)
(.leaf ⟨26927,21,(.group 9 776 false)⟩))
(.branch 26968
(.leaf ⟨26948,20,(.group 9 681 false)⟩)
(.leaf ⟨26968,20,(.group 9 680 false)⟩))))
(.branch 27077
(.branch 27031
(.branch 27011
(.leaf ⟨26988,23,(.group 7 900 false)⟩)
(.leaf ⟨27011,20,(.group 9 679 false)⟩))
(.branch 27054
(.leaf ⟨27031,23,(.group 7 899 false)⟩)
(.leaf ⟨27054,23,(.group 7 898 false)⟩)))
(.branch 27120
(.branch 27099
(.leaf ⟨27077,22,(.group 9 920 false)⟩)
(.leaf ⟨27099,21,(.group 9 775 false)⟩))
(.branch 27139
(.leaf ⟨27120,19,(.group 9 558 false)⟩)
(.leaf ⟨27139,21,(.group 9 774 false)⟩)))))
(.branch 27333
(.branch 27249
(.branch 27206
(.branch 27183
(.leaf ⟨27160,23,(.group 7 897 false)⟩)
(.leaf ⟨27183,23,(.group 7 896 false)⟩))
(.branch 27227
(.leaf ⟨27206,21,(.group 9 773 false)⟩)
(.leaf ⟨27227,22,(.group 9 919 false)⟩)))
(.branch 27289
(.branch 27268
(.leaf ⟨27249,19,(.group 9 557 false)⟩)
(.leaf ⟨27268,21,(.group 9 772 false)⟩))
(.branch 27311
(.leaf ⟨27289,22,(.group 9 918 false)⟩)
(.leaf ⟨27311,22,(.group 9 917 false)⟩))))
(.branch 27415
(.branch 27373
(.branch 27355
(.leaf ⟨27333,22,(.group 9 916 false)⟩)
(.leaf ⟨27355,18,(.group 9 487 false)⟩))
(.branch 27396
(.leaf ⟨27373,23,(.group 7 895 false)⟩)
(.leaf ⟨27396,19,(.group 9 556 false)⟩)))
(.branch 27458
(.branch 27438
(.leaf ⟨27415,23,(.group 7 894 false)⟩)
(.leaf ⟨27438,20,(.group 9 678 false)⟩))
(.branch 27478
(.leaf ⟨27458,20,(.group 9 677 false)⟩)
(.leaf ⟨27478,21,(.group 9 771 false)⟩)))))))

theorem tree21_checked : tree21.check 26162 27499 = true := by decide +kernel

def tree22 : Tree := (.branch 28163
(.branch 27831
(.branch 27673
(.branch 27584
(.branch 27543
(.branch 27520
(.leaf ⟨27499,21,(.group 9 770 false)⟩)
(.leaf ⟨27520,23,(.group 7 893 false)⟩))
(.branch 27563
(.leaf ⟨27543,20,(.group 9 676 false)⟩)
(.leaf ⟨27563,21,(.group 9 769 false)⟩)))
(.branch 27629
(.branch 27607
(.leaf ⟨27584,23,(.group 7 892 false)⟩)
(.leaf ⟨27607,22,(.group 9 915 false)⟩))
(.branch 27651
(.leaf ⟨27629,22,(.group 9 914 false)⟩)
(.leaf ⟨27651,22,(.group 9 913 false)⟩))))
(.branch 27748
(.branch 27715
(.branch 27695
(.leaf ⟨27673,22,(.group 9 912 false)⟩)
(.leaf ⟨27695,20,(.group 9 675 false)⟩))
(.branch 27730
(.leaf ⟨27715,15,(.group 10 168 false)⟩)
(.leaf ⟨27730,18,(.group 9 486 false)⟩)))
(.branch 27789
(.branch 27768
(.leaf ⟨27748,20,(.group 9 674 false)⟩)
(.leaf ⟨27768,21,(.group 9 768 false)⟩))
(.branch 27808
(.leaf ⟨27789,19,(.group 9 555 false)⟩)
(.leaf ⟨27808,23,(.group 7 891 false)⟩)))))
(.branch 28003
(.branch 27916
(.branch 27872
(.branch 27854
(.leaf ⟨27831,23,(.group 7 890 false)⟩)
(.leaf ⟨27854,18,(.group 9 485 false)⟩))
(.branch 27893
(.leaf ⟨27872,21,(.group 9 767 false)⟩)
(.leaf ⟨27893,23,(.group 7 889 false)⟩)))
(.branch 27961
(.branch 27939
(.leaf ⟨27916,23,(.group 7 888 false)⟩)
(.leaf ⟨27939,22,(.group 9 911 false)⟩))
(.branch 27980
(.leaf ⟨27961,19,(.group 9 554 false)⟩)
(.leaf ⟨27980,23,(.group 7 887 false)⟩))))
(.branch 28086
(.branch 28044
(.branch 28024
(.leaf ⟨28003,21,(.group 9 766 false)⟩)
(.leaf ⟨28024,20,(.group 9 673 false)⟩))
(.branch 28066
(.leaf ⟨28044,22,(.group 9 910 false)⟩)
(.leaf ⟨28066,20,(.group 9 672 false)⟩)))
(.branch 28128
(.branch 28105
(.leaf ⟨28086,19,(.group 9 553 false)⟩)
(.leaf ⟨28105,23,(.group 7 886 false)⟩))
(.branch 28140
(.leaf ⟨28128,12,(.group 10 83 false)⟩)
(.leaf ⟨28140,23,(.group 7 885 false)⟩))))))
(.branch 28494
(.branch 28333
(.branch 28252
(.branch 28207
(.branch 28186
(.leaf ⟨28163,23,(.group 7 884 false)⟩)
(.leaf ⟨28186,21,(.group 9 765 false)⟩))
(.branch 28229
(.leaf ⟨28207,22,(.group 9 909 false)⟩)
(.leaf ⟨28229,23,(.group 7 883 false)⟩)))
(.branch 28297
(.branch 28275
(.leaf ⟨28252,23,(.group 7 882 false)⟩)
(.leaf ⟨28275,22,(.group 9 908 false)⟩))
(.branch 28316
(.leaf ⟨28297,19,(.group 9 552 false)⟩)
(.leaf ⟨28316,17,(.group 10 263 false)⟩))))
(.branch 28415
(.branch 28370
(.branch 28352
(.leaf ⟨28333,19,(.group 9 551 false)⟩)
(.leaf ⟨28352,18,(.group 9 484 false)⟩))
(.branch 28392
(.leaf ⟨28370,22,(.group 9 907 false)⟩)
(.leaf ⟨28392,23,(.group 7 881 false)⟩)))
(.branch 28450
(.branch 28435
(.leaf ⟨28415,20,(.group 9 671 false)⟩)
(.leaf ⟨28435,15,(.group 10 167 false)⟩))
(.branch 28472
(.leaf ⟨28450,22,(.group 9 906 false)⟩)
(.leaf ⟨28472,22,(.group 9 905 false)⟩)))))
(.branch 28667
(.branch 28581
(.branch 28536
(.branch 28515
(.leaf ⟨28494,21,(.group 9 764 false)⟩)
(.leaf ⟨28515,21,(.group 9 763 false)⟩))
(.branch 28558
(.leaf ⟨28536,22,(.group 9 904 false)⟩)
(.leaf ⟨28558,23,(.group 7 880 false)⟩)))
(.branch 28624
(.branch 28604
(.leaf ⟨28581,23,(.group 7 879 false)⟩)
(.leaf ⟨28604,20,(.group 9 670 false)⟩))
(.branch 28644
(.leaf ⟨28624,20,(.group 9 669 false)⟩)
(.leaf ⟨28644,23,(.group 7 878 false)⟩))))
(.branch 28741
(.branch 28705
(.branch 28686
(.leaf ⟨28667,19,(.group 9 550 false)⟩)
(.leaf ⟨28686,19,(.group 9 549 false)⟩))
(.branch 28718
(.leaf ⟨28705,13,(.group 10 112 false)⟩)
(.leaf ⟨28718,23,(.group 7 877 false)⟩)))
(.branch 28785
(.branch 28764
(.leaf ⟨28741,23,(.group 7 876 false)⟩)
(.leaf ⟨28764,21,(.group 9 762 false)⟩))
(.branch 28805
(.leaf ⟨28785,20,(.group 9 668 false)⟩)
(.leaf ⟨28805,22,(.group 9 903 false)⟩)))))))

theorem tree22_checked : tree22.check 27499 28827 = true := by decide +kernel

def tree23 : Tree := (.branch 29470
(.branch 29143
(.branch 28992
(.branch 28917
(.branch 28872
(.branch 28849
(.leaf ⟨28827,22,(.group 9 902 false)⟩)
(.leaf ⟨28849,23,(.group 7 875 false)⟩))
(.branch 28894
(.leaf ⟨28872,22,(.group 9 901 false)⟩)
(.leaf ⟨28894,23,(.group 7 874 false)⟩)))
(.branch 28959
(.branch 28938
(.leaf ⟨28917,21,(.group 9 761 false)⟩)
(.leaf ⟨28938,21,(.group 9 760 false)⟩))
(.branch 28978
(.leaf ⟨28959,19,(.group 9 548 false)⟩)
(.leaf ⟨28978,14,(.group 10 144 false)⟩))))
(.branch 29068
(.branch 29033
(.branch 29012
(.leaf ⟨28992,20,(.group 9 667 false)⟩)
(.leaf ⟨29012,21,(.group 9 759 false)⟩))
(.branch 29055
(.leaf ⟨29033,22,(.group 9 900 false)⟩)
(.leaf ⟨29055,13,(.group 10 111 false)⟩)))
(.branch 29105
(.branch 29087
(.leaf ⟨29068,19,(.group 9 547 false)⟩)
(.leaf ⟨29087,18,(.group 9 483 false)⟩))
(.branch 29121
(.leaf ⟨29105,16,(.group 10 213 false)⟩)
(.leaf ⟨29121,22,(.group 9 899 false)⟩)))))
(.branch 29302
(.branch 29219
(.branch 29184
(.branch 29163
(.leaf ⟨29143,20,(.group 9 666 false)⟩)
(.leaf ⟨29163,21,(.group 9 758 false)⟩))
(.branch 29204
(.leaf ⟨29184,20,(.group 9 665 false)⟩)
(.leaf ⟨29204,15,(.group 10 166 false)⟩)))
(.branch 29259
(.branch 29238
(.leaf ⟨29219,19,(.group 9 546 false)⟩)
(.leaf ⟨29238,21,(.group 9 757 false)⟩))
(.branch 29281
(.leaf ⟨29259,22,(.group 9 898 false)⟩)
(.leaf ⟨29281,21,(.group 9 756 false)⟩))))
(.branch 29383
(.branch 29338
(.branch 29319
(.leaf ⟨29302,17,(.group 9 399 false)⟩)
(.leaf ⟨29319,19,(.group 9 545 false)⟩))
(.branch 29360
(.leaf ⟨29338,22,(.group 9 897 false)⟩)
(.leaf ⟨29360,23,(.group 7 873 false)⟩)))
(.branch 29427
(.branch 29406
(.leaf ⟨29383,23,(.group 7 872 false)⟩)
(.leaf ⟨29406,21,(.group 9 755 false)⟩))
(.branch 29449
(.leaf ⟨29427,22,(.group 9 896 false)⟩)
(.leaf ⟨29449,21,(.group 9 754 false)⟩))))))
(.branch 29797
(.branch 29639
(.branch 29557
(.branch 29511
(.branch 29490
(.leaf ⟨29470,20,(.group 9 664 false)⟩)
(.leaf ⟨29490,21,(.group 9 753 false)⟩))
(.branch 29534
(.leaf ⟨29511,23,(.group 7 871 false)⟩)
(.leaf ⟨29534,23,(.group 7 870 false)⟩)))
(.branch 29601
(.branch 29578
(.leaf ⟨29557,21,(.group 9 752 false)⟩)
(.leaf ⟨29578,23,(.group 7 869 false)⟩))
(.branch 29621
(.leaf ⟨29601,20,(.group 9 663 false)⟩)
(.leaf ⟨29621,18,(.group 9 482 false)⟩))))
(.branch 29711
(.branch 29672
(.branch 29661
(.leaf ⟨29639,22,(.group 9 895 false)⟩)
(.leaf ⟨29661,11,(.group 10 56 false)⟩))
(.branch 29692
(.leaf ⟨29672,20,(.group 9 662 false)⟩)
(.leaf ⟨29692,19,(.group 9 544 false)⟩)))
(.branch 29755
(.branch 29734
(.leaf ⟨29711,23,(.group 7 868 false)⟩)
(.leaf ⟨29734,21,(.group 9 751 false)⟩))
(.branch 29778
(.leaf ⟨29755,23,(.group 7 867 false)⟩)
(.leaf ⟨29778,19,(.group 9 543 false)⟩)))))
(.branch 29961
(.branch 29877
(.branch 29840
(.branch 29819
(.leaf ⟨29797,22,(.group 9 894 false)⟩)
(.leaf ⟨29819,21,(.group 9 750 false)⟩))
(.branch 29860
(.leaf ⟨29840,20,(.group 9 661 false)⟩)
(.leaf ⟨29860,17,(.group 9 398 false)⟩)))
(.branch 29921
(.branch 29899
(.leaf ⟨29877,22,(.group 9 893 false)⟩)
(.leaf ⟨29899,22,(.group 9 892 false)⟩))
(.branch 29943
(.leaf ⟨29921,22,(.group 9 891 false)⟩)
(.leaf ⟨29943,18,(.group 9 481 false)⟩))))
(.branch 30038
(.branch 30002
(.branch 29981
(.leaf ⟨29961,20,(.group 9 660 false)⟩)
(.leaf ⟨29981,21,(.group 9 749 false)⟩))
(.branch 30017
(.leaf ⟨30002,15,(.group 10 165 false)⟩)
(.leaf ⟨30017,21,(.group 9 748 false)⟩)))
(.branch 30081
(.branch 30059
(.leaf ⟨30038,21,(.group 9 747 false)⟩)
(.leaf ⟨30059,22,(.group 9 890 false)⟩))
(.branch 30102
(.leaf ⟨30081,21,(.group 9 746 false)⟩)
(.leaf ⟨30102,17,(.group 9 397 false)⟩)))))))

theorem tree23_checked : tree23.check 28827 30119 = true := by decide +kernel

def tree24 : Tree := (.branch 30742
(.branch 30428
(.branch 30286
(.branch 30205
(.branch 30163
(.branch 30142
(.leaf ⟨30119,23,(.group 7 866 false)⟩)
(.leaf ⟨30142,21,(.group 9 745 false)⟩))
(.branch 30182
(.leaf ⟨30163,19,(.group 9 542 false)⟩)
(.leaf ⟨30182,23,(.group 7 865 false)⟩)))
(.branch 30244
(.branch 30222
(.leaf ⟨30205,17,(.group 9 396 false)⟩)
(.leaf ⟨30222,22,(.group 9 889 false)⟩))
(.branch 30267
(.leaf ⟨30244,23,(.group 7 864 false)⟩)
(.leaf ⟨30267,19,(.group 9 541 false)⟩))))
(.branch 30352
(.branch 30316
(.branch 30309
(.leaf ⟨30286,23,(.group 7 863 false)⟩)
(.leaf ⟨30309,7,(.group 8 8 false)⟩))
(.branch 30335
(.leaf ⟨30316,19,(.group 9 540 false)⟩)
(.leaf ⟨30335,17,(.group 9 395 false)⟩)))
(.branch 30387
(.branch 30369
(.leaf ⟨30352,17,(.group 9 394 false)⟩)
(.leaf ⟨30369,18,(.group 9 480 false)⟩))
(.branch 30409
(.leaf ⟨30387,22,(.group 9 888 false)⟩)
(.leaf ⟨30409,19,(.group 9 539 false)⟩)))))
(.branch 30584
(.branch 30500
(.branch 30464
(.branch 30447
(.leaf ⟨30428,19,(.group 9 538 false)⟩)
(.leaf ⟨30447,17,(.group 9 393 false)⟩))
(.branch 30486
(.leaf ⟨30464,22,(.group 9 887 false)⟩)
(.leaf ⟨30486,14,(.group 10 143 false)⟩)))
(.branch 30543
(.branch 30523
(.leaf ⟨30500,23,(.group 7 862 false)⟩)
(.leaf ⟨30523,20,(.group 9 659 false)⟩))
(.branch 30562
(.leaf ⟨30543,19,(.group 9 537 false)⟩)
(.leaf ⟨30562,22,(.group 9 886 false)⟩))))
(.branch 30664
(.branch 30627
(.branch 30606
(.leaf ⟨30584,22,(.group 9 885 false)⟩)
(.leaf ⟨30606,21,(.group 9 744 false)⟩))
(.branch 30647
(.leaf ⟨30627,20,(.group 9 658 false)⟩)
(.leaf ⟨30647,17,(.group 9 392 false)⟩)))
(.branch 30702
(.branch 30684
(.leaf ⟨30664,20,(.group 9 657 false)⟩)
(.leaf ⟨30684,18,(.group 9 479 false)⟩))
(.branch 30720
(.leaf ⟨30702,18,(.group 9 478 false)⟩)
(.leaf ⟨30720,22,(.group 9 884 false)⟩))))))
(.branch 31061
(.branch 30908
(.branch 30822
(.branch 30779
(.branch 30762
(.leaf ⟨30742,20,(.group 9 656 false)⟩)
(.leaf ⟨30762,17,(.group 9 391 false)⟩))
(.branch 30801
(.leaf ⟨30779,22,(.group 9 883 false)⟩)
(.leaf ⟨30801,21,(.group 9 743 false)⟩)))
(.branch 30864
(.branch 30844
(.leaf ⟨30822,22,(.group 9 882 false)⟩)
(.leaf ⟨30844,20,(.group 9 655 false)⟩))
(.branch 30885
(.leaf ⟨30864,21,(.group 9 742 false)⟩)
(.leaf ⟨30885,23,(.group 7 861 false)⟩))))
(.branch 30989
(.branch 30952
(.branch 30929
(.leaf ⟨30908,21,(.group 9 741 false)⟩)
(.leaf ⟨30929,23,(.group 7 860 false)⟩))
(.branch 30968
(.leaf ⟨30952,16,(.group 10 212 false)⟩)
(.leaf ⟨30968,21,(.group 9 740 false)⟩)))
(.branch 31027
(.branch 31010
(.leaf ⟨30989,21,(.group 9 739 false)⟩)
(.leaf ⟨31010,17,(.group 9 390 false)⟩))
(.branch 31046
(.leaf ⟨31027,19,(.group 9 536 false)⟩)
(.leaf ⟨31046,15,(.group 10 164 false)⟩)))))
(.branch 31221
(.branch 31135
(.branch 31096
(.branch 31080
(.leaf ⟨31061,19,(.group 9 535 false)⟩)
(.leaf ⟨31080,16,(.group 10 211 false)⟩))
(.branch 31117
(.leaf ⟨31096,21,(.group 9 738 false)⟩)
(.leaf ⟨31117,18,(.group 9 477 false)⟩)))
(.branch 31179
(.branch 31157
(.leaf ⟨31135,22,(.group 9 881 false)⟩)
(.leaf ⟨31157,22,(.group 9 880 false)⟩))
(.branch 31198
(.leaf ⟨31179,19,(.group 9 534 false)⟩)
(.leaf ⟨31198,23,(.group 7 859 false)⟩))))
(.branch 31305
(.branch 31264
(.branch 31244
(.leaf ⟨31221,23,(.group 7 858 false)⟩)
(.leaf ⟨31244,20,(.group 9 654 false)⟩))
(.branch 31284
(.leaf ⟨31264,20,(.group 9 653 false)⟩)
(.leaf ⟨31284,21,(.group 9 737 false)⟩)))
(.branch 31344
(.branch 31323
(.leaf ⟨31305,18,(.group 9 476 false)⟩)
(.leaf ⟨31323,21,(.group 9 736 false)⟩))
(.branch 31358
(.leaf ⟨31344,14,(.group 10 142 false)⟩)
(.leaf ⟨31358,21,(.group 9 735 false)⟩)))))))

theorem tree24_checked : tree24.check 30119 31379 = true := by decide +kernel

def tree25 : Tree := (.branch 32040
(.branch 31708
(.branch 31545
(.branch 31464
(.branch 31423
(.branch 31401
(.leaf ⟨31379,22,(.group 9 879 false)⟩)
(.leaf ⟨31401,22,(.group 9 878 false)⟩))
(.branch 31443
(.leaf ⟨31423,20,(.group 9 652 false)⟩)
(.leaf ⟨31443,21,(.group 9 734 false)⟩)))
(.branch 31508
(.branch 31485
(.leaf ⟨31464,21,(.group 9 733 false)⟩)
(.leaf ⟨31485,23,(.group 7 857 false)⟩))
(.branch 31525
(.leaf ⟨31508,17,(.group 9 389 false)⟩)
(.leaf ⟨31525,20,(.group 9 651 false)⟩))))
(.branch 31629
(.branch 31585
(.branch 31563
(.leaf ⟨31545,18,(.group 9 475 false)⟩)
(.leaf ⟨31563,22,(.group 9 877 false)⟩))
(.branch 31606
(.leaf ⟨31585,21,(.group 9 732 false)⟩)
(.leaf ⟨31606,23,(.group 7 856 false)⟩)))
(.branch 31663
(.branch 31647
(.leaf ⟨31629,18,(.group 9 474 false)⟩)
(.leaf ⟨31647,16,(.group 10 210 false)⟩))
(.branch 31686
(.leaf ⟨31663,23,(.group 7 855 false)⟩)
(.leaf ⟨31686,22,(.group 9 876 false)⟩)))))
(.branch 31879
(.branch 31795
(.branch 31749
(.branch 31728
(.leaf ⟨31708,20,(.group 9 650 false)⟩)
(.leaf ⟨31728,21,(.group 9 731 false)⟩))
(.branch 31772
(.leaf ⟨31749,23,(.group 7 854 false)⟩)
(.leaf ⟨31772,23,(.group 7 853 false)⟩)))
(.branch 31840
(.branch 31817
(.leaf ⟨31795,22,(.group 9 875 false)⟩)
(.leaf ⟨31817,23,(.group 7 852 false)⟩))
(.branch 31856
(.leaf ⟨31840,16,(.group 10 209 false)⟩)
(.leaf ⟨31856,23,(.group 7 851 false)⟩))))
(.branch 31956
(.branch 31923
(.branch 31900
(.leaf ⟨31879,21,(.group 9 730 false)⟩)
(.leaf ⟨31900,23,(.group 7 850 false)⟩))
(.branch 31941
(.leaf ⟨31923,18,(.group 9 473 false)⟩)
(.leaf ⟨31941,15,(.group 10 163 false)⟩)))
(.branch 31999
(.branch 31976
(.leaf ⟨31956,20,(.group 9 649 false)⟩)
(.leaf ⟨31976,23,(.group 7 849 false)⟩))
(.branch 32018
(.leaf ⟨31999,19,(.group 9 533 false)⟩)
(.leaf ⟨32018,22,(.group 9 874 false)⟩))))))
(.branch 32365
(.branch 32195
(.branch 32128
(.branch 32084
(.branch 32061
(.leaf ⟨32040,21,(.group 9 729 false)⟩)
(.leaf ⟨32061,23,(.group 7 848 false)⟩))
(.branch 32105
(.leaf ⟨32084,21,(.group 9 728 false)⟩)
(.leaf ⟨32105,23,(.group 7 847 false)⟩)))
(.branch 32155
(.branch 32142
(.leaf ⟨32128,14,(.group 10 141 false)⟩)
(.leaf ⟨32142,13,(.group 10 110 false)⟩))
(.branch 32174
(.leaf ⟨32155,19,(.group 9 532 false)⟩)
(.leaf ⟨32174,21,(.group 9 727 false)⟩))))
(.branch 32281
(.branch 32237
(.branch 32218
(.leaf ⟨32195,23,(.group 7 846 false)⟩)
(.leaf ⟨32218,19,(.group 9 531 false)⟩))
(.branch 32259
(.leaf ⟨32237,22,(.group 9 873 false)⟩)
(.leaf ⟨32259,22,(.group 9 872 false)⟩)))
(.branch 32321
(.branch 32299
(.leaf ⟨32281,18,(.group 9 472 false)⟩)
(.leaf ⟨32299,22,(.group 9 871 false)⟩))
(.branch 32343
(.leaf ⟨32321,22,(.group 9 870 false)⟩)
(.leaf ⟨32343,22,(.group 9 869 false)⟩)))))
(.branch 32503
(.branch 32436
(.branch 32400
(.branch 32385
(.leaf ⟨32365,20,(.group 9 648 false)⟩)
(.leaf ⟨32385,15,(.group 9 255 false)⟩))
(.branch 32419
(.leaf ⟨32400,19,(.group 9 530 false)⟩)
(.leaf ⟨32419,17,(.group 9 388 false)⟩)))
(.branch 32472
(.branch 32452
(.leaf ⟨32436,16,(.group 10 208 false)⟩)
(.leaf ⟨32452,20,(.group 9 647 false)⟩))
(.branch 32489
(.leaf ⟨32472,17,(.group 9 387 false)⟩)
(.leaf ⟨32489,14,(.group 10 140 false)⟩))))
(.branch 32581
(.branch 32546
(.branch 32524
(.leaf ⟨32503,21,(.group 9 726 false)⟩)
(.leaf ⟨32524,22,(.group 9 868 false)⟩))
(.branch 32560
(.leaf ⟨32546,14,(.group 10 139 false)⟩)
(.leaf ⟨32560,21,(.group 9 725 false)⟩)))
(.branch 32621
(.branch 32599
(.leaf ⟨32581,18,(.group 9 471 false)⟩)
(.leaf ⟨32599,22,(.group 9 867 false)⟩))
(.branch 32634
(.leaf ⟨32621,13,(.group 10 109 false)⟩)
(.leaf ⟨32634,22,(.group 9 866 false)⟩)))))))

theorem tree25_checked : tree25.check 31379 32656 = true := by decide +kernel

def tree26 : Tree := (.branch 33245
(.branch 32946
(.branch 32796
(.branch 32724
(.branch 32697
(.branch 32675
(.leaf ⟨32656,19,(.group 9 529 false)⟩)
(.leaf ⟨32675,22,(.group 9 865 false)⟩))
(.branch 32716
(.leaf ⟨32697,19,(.group 9 528 false)⟩)
(.leaf ⟨32716,8,(.group 10 24 false)⟩)))
(.branch 32756
(.branch 32738
(.leaf ⟨32724,14,(.group 8 203 false)⟩)
(.leaf ⟨32738,18,(.group 9 470 false)⟩))
(.branch 32776
(.leaf ⟨32756,20,(.group 9 646 false)⟩)
(.leaf ⟨32776,20,(.group 9 645 false)⟩))))
(.branch 32868
(.branch 32837
(.branch 32817
(.leaf ⟨32796,21,(.group 9 724 false)⟩)
(.leaf ⟨32817,20,(.group 9 644 false)⟩))
(.branch 32851
(.leaf ⟨32837,14,(.group 10 138 false)⟩)
(.leaf ⟨32851,17,(.group 9 386 false)⟩)))
(.branch 32906
(.branch 32885
(.leaf ⟨32868,17,(.group 9 385 false)⟩)
(.leaf ⟨32885,21,(.group 9 723 false)⟩))
(.branch 32924
(.leaf ⟨32906,18,(.group 9 469 false)⟩)
(.leaf ⟨32924,22,(.group 9 864 false)⟩)))))
(.branch 33088
(.branch 33017
(.branch 32981
(.branch 32959
(.leaf ⟨32946,13,(.group 10 108 false)⟩)
(.leaf ⟨32959,22,(.group 9 863 false)⟩))
(.branch 33000
(.leaf ⟨32981,19,(.group 9 527 false)⟩)
(.leaf ⟨33000,17,(.group 9 384 false)⟩)))
(.branch 33049
(.branch 33035
(.leaf ⟨33017,18,(.group 9 468 false)⟩)
(.leaf ⟨33035,14,(.group 10 137 false)⟩))
(.branch 33071
(.leaf ⟨33049,22,(.group 9 862 false)⟩)
(.leaf ⟨33071,17,(.group 9 383 false)⟩))))
(.branch 33166
(.branch 33125
(.branch 33103
(.leaf ⟨33088,15,(.group 9 254 false)⟩)
(.leaf ⟨33103,22,(.group 9 861 false)⟩))
(.branch 33145
(.leaf ⟨33125,20,(.group 9 643 false)⟩)
(.leaf ⟨33145,21,(.group 9 722 false)⟩)))
(.branch 33208
(.branch 33187
(.leaf ⟨33166,21,(.group 9 721 false)⟩)
(.leaf ⟨33187,21,(.group 9 720 false)⟩))
(.branch 33228
(.leaf ⟨33208,20,(.group 9 642 false)⟩)
(.leaf ⟨33228,17,(.group 9 382 false)⟩))))))
(.branch 33552
(.branch 33407
(.branch 33324
(.branch 33283
(.branch 33265
(.leaf ⟨33245,20,(.group 9 641 false)⟩)
(.leaf ⟨33265,18,(.group 9 467 false)⟩))
(.branch 33305
(.leaf ⟨33283,22,(.group 9 860 false)⟩)
(.leaf ⟨33305,19,(.group 9 526 false)⟩)))
(.branch 33365
(.branch 33345
(.leaf ⟨33324,21,(.group 9 719 false)⟩)
(.leaf ⟨33345,20,(.group 9 640 false)⟩))
(.branch 33385
(.leaf ⟨33365,20,(.group 9 639 false)⟩)
(.leaf ⟨33385,22,(.group 9 859 false)⟩))))
(.branch 33473
(.branch 33436
(.branch 33428
(.leaf ⟨33407,21,(.group 8 862 false)⟩)
(.leaf ⟨33428,8,(.group 8 22 false)⟩))
(.branch 33456
(.leaf ⟨33436,20,(.group 9 638 false)⟩)
(.leaf ⟨33456,17,(.group 9 381 false)⟩)))
(.branch 33510
(.branch 33494
(.leaf ⟨33473,21,(.group 8 861 false)⟩)
(.leaf ⟨33494,16,(.group 9 321 false)⟩))
(.branch 33532
(.leaf ⟨33510,22,(.group 9 858 false)⟩)
(.leaf ⟨33532,20,(.group 9 637 false)⟩)))))
(.branch 33709
(.branch 33630
(.branch 33590
(.branch 33572
(.leaf ⟨33552,20,(.group 9 636 false)⟩)
(.leaf ⟨33572,18,(.group 9 466 false)⟩))
(.branch 33610
(.leaf ⟨33590,20,(.group 9 635 false)⟩)
(.leaf ⟨33610,20,(.group 9 634 false)⟩)))
(.branch 33668
(.branch 33647
(.leaf ⟨33630,17,(.group 9 380 false)⟩)
(.leaf ⟨33647,21,(.group 8 860 false)⟩))
(.branch 33688
(.leaf ⟨33668,20,(.group 9 633 false)⟩)
(.leaf ⟨33688,21,(.group 8 859 false)⟩))))
(.branch 33787
(.branch 33745
(.branch 33730
(.leaf ⟨33709,21,(.group 8 858 false)⟩)
(.leaf ⟨33730,15,(.group 9 253 false)⟩))
(.branch 33767
(.leaf ⟨33745,22,(.group 9 857 false)⟩)
(.leaf ⟨33767,20,(.group 9 632 false)⟩)))
(.branch 33829
(.branch 33807
(.leaf ⟨33787,20,(.group 9 631 false)⟩)
(.leaf ⟨33807,22,(.group 9 856 false)⟩))
(.branch 33850
(.leaf ⟨33829,21,(.group 8 857 false)⟩)
(.leaf ⟨33850,16,(.group 9 320 false)⟩)))))))

theorem tree26_checked : tree26.check 32656 33866 = true := by decide +kernel

def tree27 : Tree := (.branch 34497
(.branch 34186
(.branch 34032
(.branch 33952
(.branch 33909
(.branch 33887
(.leaf ⟨33866,21,(.group 8 856 false)⟩)
(.leaf ⟨33887,22,(.group 9 855 false)⟩))
(.branch 33931
(.leaf ⟨33909,22,(.group 8 1015 false)⟩)
(.leaf ⟨33931,21,(.group 8 855 false)⟩)))
(.branch 33994
(.branch 33974
(.leaf ⟨33952,22,(.group 8 1014 false)⟩)
(.leaf ⟨33974,20,(.group 9 630 false)⟩))
(.branch 34013
(.leaf ⟨33994,19,(.group 9 525 false)⟩)
(.leaf ⟨34013,19,(.group 9 524 false)⟩))))
(.branch 34109
(.branch 34068
(.branch 34053
(.leaf ⟨34032,21,(.group 8 854 false)⟩)
(.leaf ⟨34053,15,(.group 9 252 false)⟩))
(.branch 34088
(.leaf ⟨34068,20,(.group 9 629 false)⟩)
(.leaf ⟨34088,21,(.group 8 853 false)⟩)))
(.branch 34150
(.branch 34128
(.leaf ⟨34109,19,(.group 9 523 false)⟩)
(.leaf ⟨34128,22,(.group 8 1013 false)⟩))
(.branch 34167
(.leaf ⟨34150,17,(.group 9 379 false)⟩)
(.leaf ⟨34167,19,(.group 9 522 false)⟩)))))
(.branch 34350
(.branch 34269
(.branch 34227
(.branch 34205
(.leaf ⟨34186,19,(.group 9 521 false)⟩)
(.leaf ⟨34205,22,(.group 8 1012 false)⟩))
(.branch 34247
(.leaf ⟨34227,20,(.group 9 628 false)⟩)
(.leaf ⟨34247,22,(.group 8 1011 false)⟩)))
(.branch 34311
(.branch 34289
(.leaf ⟨34269,20,(.group 9 627 false)⟩)
(.leaf ⟨34289,22,(.group 8 1010 false)⟩))
(.branch 34328
(.leaf ⟨34311,17,(.group 9 378 false)⟩)
(.leaf ⟨34328,22,(.group 8 1009 false)⟩))))
(.branch 34427
(.branch 34383
(.branch 34366
(.leaf ⟨34350,16,(.group 9 319 false)⟩)
(.leaf ⟨34366,17,(.group 9 377 false)⟩))
(.branch 34405
(.leaf ⟨34383,22,(.group 8 1008 false)⟩)
(.leaf ⟨34405,22,(.group 8 1007 false)⟩)))
(.branch 34459
(.branch 34445
(.leaf ⟨34427,18,(.group 9 465 false)⟩)
(.leaf ⟨34445,14,(.group 10 136 false)⟩))
(.branch 34478
(.leaf ⟨34459,19,(.group 9 520 false)⟩)
(.leaf ⟨34478,19,(.group 9 519 false)⟩))))))
(.branch 34812
(.branch 34658
(.branch 34581
(.branch 34540
(.branch 34518
(.leaf ⟨34497,21,(.group 8 852 false)⟩)
(.leaf ⟨34518,22,(.group 8 1006 false)⟩))
(.branch 34560
(.leaf ⟨34540,20,(.group 9 626 false)⟩)
(.leaf ⟨34560,21,(.group 8 851 false)⟩)))
(.branch 34619
(.branch 34601
(.leaf ⟨34581,20,(.group 9 625 false)⟩)
(.leaf ⟨34601,18,(.group 9 464 false)⟩))
(.branch 34639
(.leaf ⟨34619,20,(.group 9 624 false)⟩)
(.leaf ⟨34639,19,(.group 9 518 false)⟩))))
(.branch 34733
(.branch 34692
(.branch 34674
(.leaf ⟨34658,16,(.group 9 318 false)⟩)
(.leaf ⟨34674,18,(.group 9 463 false)⟩))
(.branch 34713
(.leaf ⟨34692,21,(.group 8 850 false)⟩)
(.leaf ⟨34713,20,(.group 9 623 false)⟩)))
(.branch 34773
(.branch 34755
(.leaf ⟨34733,22,(.group 8 1005 false)⟩)
(.leaf ⟨34755,18,(.group 9 462 false)⟩))
(.branch 34793
(.leaf ⟨34773,20,(.group 9 622 false)⟩)
(.leaf ⟨34793,19,(.group 9 517 false)⟩)))))
(.branch 34965
(.branch 34884
(.branch 34850
(.branch 34832
(.leaf ⟨34812,20,(.group 9 621 false)⟩)
(.leaf ⟨34832,18,(.group 9 461 false)⟩))
(.branch 34867
(.leaf ⟨34850,17,(.group 9 376 false)⟩)
(.leaf ⟨34867,17,(.group 9 375 false)⟩)))
(.branch 34923
(.branch 34902
(.leaf ⟨34884,18,(.group 9 460 false)⟩)
(.leaf ⟨34902,21,(.group 8 849 false)⟩))
(.branch 34943
(.leaf ⟨34923,20,(.group 9 620 false)⟩)
(.leaf ⟨34943,22,(.group 8 1004 false)⟩))))
(.branch 35046
(.branch 35007
(.branch 34986
(.leaf ⟨34965,21,(.group 8 848 false)⟩)
(.leaf ⟨34986,21,(.group 8 847 false)⟩))
(.branch 35026
(.leaf ⟨35007,19,(.group 9 516 false)⟩)
(.leaf ⟨35026,20,(.group 9 619 false)⟩)))
(.branch 35086
(.branch 35067
(.leaf ⟨35046,21,(.group 8 846 false)⟩)
(.leaf ⟨35067,19,(.group 9 515 false)⟩))
(.branch 35101
(.leaf ⟨35086,15,(.group 9 251 false)⟩)
(.leaf ⟨35101,21,(.group 8 845 false)⟩)))))))

theorem tree27_checked : tree27.check 33866 35122 = true := by decide +kernel

def tree28 : Tree := (.branch 35746
(.branch 35427
(.branch 35268
(.branch 35195
(.branch 35160
(.branch 35138
(.leaf ⟨35122,16,(.group 9 317 false)⟩)
(.leaf ⟨35138,22,(.group 8 1003 false)⟩))
(.branch 35173
(.leaf ⟨35160,13,(.group 10 107 false)⟩)
(.leaf ⟨35173,22,(.group 8 1002 false)⟩)))
(.branch 35229
(.branch 35210
(.leaf ⟨35195,15,(.group 9 250 false)⟩)
(.leaf ⟨35210,19,(.group 9 514 false)⟩))
(.branch 35251
(.leaf ⟨35229,22,(.group 8 1001 false)⟩)
(.leaf ⟨35251,17,(.group 9 374 false)⟩))))
(.branch 35352
(.branch 35308
(.branch 35289
(.leaf ⟨35268,21,(.group 8 844 false)⟩)
(.leaf ⟨35289,19,(.group 9 513 false)⟩))
(.branch 35330
(.leaf ⟨35308,22,(.group 8 1000 false)⟩)
(.leaf ⟨35330,22,(.group 8 999 false)⟩)))
(.branch 35391
(.branch 35370
(.leaf ⟨35352,18,(.group 9 459 false)⟩)
(.leaf ⟨35370,21,(.group 8 843 false)⟩))
(.branch 35412
(.leaf ⟨35391,21,(.group 8 842 false)⟩)
(.leaf ⟨35412,15,(.group 9 249 false)⟩)))))
(.branch 35581
(.branch 35502
(.branch 35461
(.branch 35446
(.leaf ⟨35427,19,(.group 9 512 false)⟩)
(.leaf ⟨35446,15,(.group 9 248 false)⟩))
(.branch 35481
(.leaf ⟨35461,20,(.group 9 618 false)⟩)
(.leaf ⟨35481,21,(.group 8 841 false)⟩)))
(.branch 35541
(.branch 35524
(.leaf ⟨35502,22,(.group 8 998 false)⟩)
(.leaf ⟨35524,17,(.group 9 373 false)⟩))
(.branch 35563
(.leaf ⟨35541,22,(.group 8 997 false)⟩)
(.leaf ⟨35563,18,(.group 9 458 false)⟩))))
(.branch 35663
(.branch 35624
(.branch 35603
(.leaf ⟨35581,22,(.group 8 996 false)⟩)
(.leaf ⟨35603,21,(.group 8 840 false)⟩))
(.branch 35646
(.leaf ⟨35624,22,(.group 8 995 false)⟩)
(.leaf ⟨35646,17,(.group 9 372 false)⟩)))
(.branch 35707
(.branch 35685
(.leaf ⟨35663,22,(.group 8 994 false)⟩)
(.leaf ⟨35685,22,(.group 8 993 false)⟩))
(.branch 35725
(.leaf ⟨35707,18,(.group 9 457 false)⟩)
(.leaf ⟨35725,21,(.group 8 839 false)⟩))))))
(.branch 36034
(.branch 35900
(.branch 35822
(.branch 35779
(.branch 35761
(.leaf ⟨35746,15,(.group 9 247 false)⟩)
(.leaf ⟨35761,18,(.group 9 456 false)⟩))
(.branch 35800
(.leaf ⟨35779,21,(.group 8 838 false)⟩)
(.leaf ⟨35800,22,(.group 8 992 false)⟩)))
(.branch 35863
(.branch 35844
(.leaf ⟨35822,22,(.group 8 991 false)⟩)
(.leaf ⟨35844,19,(.group 9 511 false)⟩))
(.branch 35878
(.leaf ⟨35863,15,(.group 9 246 false)⟩)
(.leaf ⟨35878,22,(.group 8 990 false)⟩))))
(.branch 35973
(.branch 35933
(.branch 35922
(.leaf ⟨35900,22,(.group 8 989 false)⟩)
(.leaf ⟨35922,11,(.group 10 55 false)⟩))
(.branch 35955
(.leaf ⟨35933,22,(.group 8 988 false)⟩)
(.leaf ⟨35955,18,(.group 9 455 false)⟩)))
(.branch 36009
(.branch 35991
(.leaf ⟨35973,18,(.group 9 454 false)⟩)
(.leaf ⟨35991,18,(.group 9 453 false)⟩))
(.branch 36021
(.leaf ⟨36009,12,(.group 10 82 false)⟩)
(.leaf ⟨36021,13,(.group 10 106 false)⟩)))))
(.branch 36186
(.branch 36109
(.branch 36068
(.branch 36051
(.leaf ⟨36034,17,(.group 9 371 false)⟩)
(.leaf ⟨36051,17,(.group 9 370 false)⟩))
(.branch 36090
(.leaf ⟨36068,22,(.group 8 987 false)⟩)
(.leaf ⟨36090,19,(.group 9 510 false)⟩)))
(.branch 36150
(.branch 36131
(.leaf ⟨36109,22,(.group 8 986 false)⟩)
(.leaf ⟨36131,19,(.group 9 509 false)⟩))
(.branch 36166
(.leaf ⟨36150,16,(.group 9 316 false)⟩)
(.leaf ⟨36166,20,(.group 9 617 false)⟩))))
(.branch 36257
(.branch 36225
(.branch 36208
(.leaf ⟨36186,22,(.group 8 985 false)⟩)
(.leaf ⟨36208,17,(.group 9 369 false)⟩))
(.branch 36242
(.leaf ⟨36225,17,(.group 9 368 false)⟩)
(.leaf ⟨36242,15,(.group 9 245 false)⟩)))
(.branch 36298
(.branch 36276
(.leaf ⟨36257,19,(.group 9 508 false)⟩)
(.leaf ⟨36276,22,(.group 8 984 false)⟩))
(.branch 36318
(.leaf ⟨36298,20,(.group 9 616 false)⟩)
(.leaf ⟨36318,15,(.group 9 244 false)⟩)))))))

theorem tree28_checked : tree28.check 35122 36333 = true := by decide +kernel

def tree29 : Tree := (.branch 36950
(.branch 36638
(.branch 36493
(.branch 36415
(.branch 36373
(.branch 36355
(.leaf ⟨36333,22,(.group 8 983 false)⟩)
(.leaf ⟨36355,18,(.group 9 452 false)⟩))
(.branch 36395
(.leaf ⟨36373,22,(.group 8 982 false)⟩)
(.leaf ⟨36395,20,(.group 9 615 false)⟩)))
(.branch 36452
(.branch 36433
(.leaf ⟨36415,18,(.group 9 451 false)⟩)
(.leaf ⟨36433,19,(.group 9 507 false)⟩))
(.branch 36473
(.leaf ⟨36452,21,(.group 8 837 false)⟩)
(.leaf ⟨36473,20,(.group 9 614 false)⟩))))
(.branch 36569
(.branch 36534
(.branch 36513
(.leaf ⟨36493,20,(.group 9 613 false)⟩)
(.leaf ⟨36513,21,(.group 8 836 false)⟩))
(.branch 36552
(.leaf ⟨36534,18,(.group 9 450 false)⟩)
(.leaf ⟨36552,17,(.group 9 367 false)⟩)))
(.branch 36608
(.branch 36588
(.leaf ⟨36569,19,(.group 9 506 false)⟩)
(.leaf ⟨36588,20,(.group 9 612 false)⟩))
(.branch 36621
(.leaf ⟨36608,13,(.group 10 105 false)⟩)
(.leaf ⟨36621,17,(.group 9 366 false)⟩)))))
(.branch 36794
(.branch 36717
(.branch 36682
(.branch 36660
(.leaf ⟨36638,22,(.group 8 981 false)⟩)
(.leaf ⟨36660,22,(.group 8 980 false)⟩))
(.branch 36700
(.leaf ⟨36682,18,(.group 9 449 false)⟩)
(.leaf ⟨36700,17,(.group 9 365 false)⟩)))
(.branch 36754
(.branch 36737
(.leaf ⟨36717,20,(.group 9 611 false)⟩)
(.leaf ⟨36737,17,(.group 9 364 false)⟩))
(.branch 36774
(.leaf ⟨36754,20,(.group 9 610 false)⟩)
(.leaf ⟨36774,20,(.group 9 609 false)⟩))))
(.branch 36875
(.branch 36832
(.branch 36815
(.leaf ⟨36794,21,(.group 8 835 false)⟩)
(.leaf ⟨36815,17,(.group 9 363 false)⟩))
(.branch 36854
(.leaf ⟨36832,22,(.group 8 979 false)⟩)
(.leaf ⟨36854,21,(.group 8 834 false)⟩)))
(.branch 36908
(.branch 36891
(.leaf ⟨36875,16,(.group 9 315 false)⟩)
(.leaf ⟨36891,17,(.group 9 362 false)⟩))
(.branch 36928
(.leaf ⟨36908,20,(.group 9 608 false)⟩)
(.leaf ⟨36928,22,(.group 8 978 false)⟩))))))
(.branch 37262
(.branch 37107
(.branch 37030
(.branch 36990
(.branch 36972
(.leaf ⟨36950,22,(.group 8 977 false)⟩)
(.leaf ⟨36972,18,(.group 9 448 false)⟩))
(.branch 37010
(.leaf ⟨36990,20,(.group 9 607 false)⟩)
(.leaf ⟨37010,20,(.group 9 606 false)⟩)))
(.branch 37070
(.branch 37051
(.leaf ⟨37030,21,(.group 8 833 false)⟩)
(.leaf ⟨37051,19,(.group 9 505 false)⟩))
(.branch 37092
(.leaf ⟨37070,22,(.group 8 976 false)⟩)
(.leaf ⟨37092,15,(.group 9 243 false)⟩))))
(.branch 37185
(.branch 37146
(.branch 37129
(.leaf ⟨37107,22,(.group 8 975 false)⟩)
(.leaf ⟨37129,17,(.group 9 361 false)⟩))
(.branch 37166
(.leaf ⟨37146,20,(.group 9 605 false)⟩)
(.leaf ⟨37166,19,(.group 9 504 false)⟩)))
(.branch 37226
(.branch 37204
(.leaf ⟨37185,19,(.group 9 503 false)⟩)
(.leaf ⟨37204,22,(.group 8 974 false)⟩))
(.branch 37242
(.leaf ⟨37226,16,(.group 9 314 false)⟩)
(.leaf ⟨37242,20,(.group 9 604 false)⟩)))))
(.branch 37399
(.branch 37330
(.branch 37298
(.branch 37278
(.leaf ⟨37262,16,(.group 9 313 false)⟩)
(.leaf ⟨37278,20,(.group 9 603 false)⟩))
(.branch 37317
(.leaf ⟨37298,19,(.group 9 502 false)⟩)
(.leaf ⟨37317,13,(.group 10 104 false)⟩)))
(.branch 37362
(.branch 37343
(.leaf ⟨37330,13,(.group 10 103 false)⟩)
(.leaf ⟨37343,19,(.group 9 501 false)⟩))
(.branch 37384
(.leaf ⟨37362,22,(.group 8 973 false)⟩)
(.leaf ⟨37384,15,(.group 9 242 false)⟩))))
(.branch 37473
(.branch 37440
(.branch 37420
(.leaf ⟨37399,21,(.group 8 832 false)⟩)
(.leaf ⟨37420,20,(.group 9 602 false)⟩))
(.branch 37458
(.leaf ⟨37440,18,(.group 9 447 false)⟩)
(.leaf ⟨37458,15,(.group 9 241 false)⟩)))
(.branch 37516
(.branch 37495
(.leaf ⟨37473,22,(.group 8 972 false)⟩)
(.leaf ⟨37495,21,(.group 8 831 false)⟩))
(.branch 37537
(.leaf ⟨37516,21,(.group 8 830 false)⟩)
(.leaf ⟨37537,17,(.group 9 360 false)⟩)))))))

theorem tree29_checked : tree29.check 36333 37554 = true := by decide +kernel

def tree30 : Tree := (.branch 38143
(.branch 37830
(.branch 37697
(.branch 37620
(.branch 37583
(.branch 37571
(.leaf ⟨37554,17,(.group 9 359 false)⟩)
(.leaf ⟨37571,12,(.group 10 81 false)⟩))
(.branch 37604
(.leaf ⟨37583,21,(.group 8 829 false)⟩)
(.leaf ⟨37604,16,(.group 9 312 false)⟩)))
(.branch 37660
(.branch 37638
(.leaf ⟨37620,18,(.group 9 446 false)⟩)
(.leaf ⟨37638,22,(.group 8 971 false)⟩))
(.branch 37679
(.leaf ⟨37660,19,(.group 9 500 false)⟩)
(.leaf ⟨37679,18,(.group 9 445 false)⟩))))
(.branch 37760
(.branch 37724
(.branch 37712
(.leaf ⟨37697,15,(.group 9 240 false)⟩)
(.leaf ⟨37712,12,(.group 10 80 false)⟩))
(.branch 37742
(.leaf ⟨37724,18,(.group 9 444 false)⟩)
(.leaf ⟨37742,18,(.group 9 443 false)⟩)))
(.branch 37798
(.branch 37779
(.leaf ⟨37760,19,(.group 9 499 false)⟩)
(.leaf ⟨37779,19,(.group 9 498 false)⟩))
(.branch 37814
(.leaf ⟨37798,16,(.group 9 311 false)⟩)
(.leaf ⟨37814,16,(.group 9 310 false)⟩)))))
(.branch 37983
(.branch 37902
(.branch 37867
(.branch 37848
(.leaf ⟨37830,18,(.group 9 442 false)⟩)
(.leaf ⟨37848,19,(.group 9 497 false)⟩))
(.branch 37883
(.leaf ⟨37867,16,(.group 9 309 false)⟩)
(.leaf ⟨37883,19,(.group 9 496 false)⟩)))
(.branch 37940
(.branch 37920
(.leaf ⟨37902,18,(.group 9 441 false)⟩)
(.leaf ⟨37920,20,(.group 9 601 false)⟩))
(.branch 37961
(.leaf ⟨37940,21,(.group 8 828 false)⟩)
(.leaf ⟨37961,22,(.group 8 970 false)⟩))))
(.branch 38062
(.branch 38022
(.branch 38004
(.leaf ⟨37983,21,(.group 8 827 false)⟩)
(.leaf ⟨38004,18,(.group 9 440 false)⟩))
(.branch 38042
(.leaf ⟨38022,20,(.group 9 600 false)⟩)
(.leaf ⟨38042,20,(.group 9 599 false)⟩)))
(.branch 38099
(.branch 38081
(.leaf ⟨38062,19,(.group 9 495 false)⟩)
(.leaf ⟨38081,18,(.group 9 439 false)⟩))
(.branch 38121
(.leaf ⟨38099,22,(.group 8 969 false)⟩)
(.leaf ⟨38121,22,(.group 8 968 false)⟩))))))
(.branch 38461
(.branch 38302
(.branch 38221
(.branch 38185
(.branch 38164
(.leaf ⟨38143,21,(.group 8 826 false)⟩)
(.leaf ⟨38164,21,(.group 8 825 false)⟩))
(.branch 38200
(.leaf ⟨38185,15,(.group 9 239 false)⟩)
(.leaf ⟨38200,21,(.group 8 824 false)⟩)))
(.branch 38263
(.branch 38241
(.leaf ⟨38221,20,(.group 8 716 false)⟩)
(.leaf ⟨38241,22,(.group 8 967 false)⟩))
(.branch 38283
(.leaf ⟨38263,20,(.group 8 715 false)⟩)
(.leaf ⟨38283,19,(.group 9 494 false)⟩))))
(.branch 38386
(.branch 38342
(.branch 38322
(.leaf ⟨38302,20,(.group 8 714 false)⟩)
(.leaf ⟨38322,20,(.group 8 713 false)⟩))
(.branch 38364
(.leaf ⟨38342,22,(.group 8 966 false)⟩)
(.leaf ⟨38364,22,(.group 8 965 false)⟩)))
(.branch 38418
(.branch 38408
(.leaf ⟨38386,22,(.group 8 964 false)⟩)
(.leaf ⟨38408,10,(.group 10 43 false)⟩))
(.branch 38440
(.leaf ⟨38418,22,(.group 8 963 false)⟩)
(.leaf ⟨38440,21,(.group 8 823 false)⟩)))))
(.branch 38622
(.branch 38541
(.branch 38501
(.branch 38482
(.leaf ⟨38461,21,(.group 8 822 false)⟩)
(.leaf ⟨38482,19,(.group 8 596 false)⟩))
(.branch 38519
(.leaf ⟨38501,18,(.group 9 438 false)⟩)
(.leaf ⟨38519,22,(.group 8 962 false)⟩)))
(.branch 38580
(.branch 38558
(.leaf ⟨38541,17,(.group 9 358 false)⟩)
(.leaf ⟨38558,22,(.group 8 961 false)⟩))
(.branch 38600
(.leaf ⟨38580,20,(.group 8 712 false)⟩)
(.leaf ⟨38600,22,(.group 8 960 false)⟩))))
(.branch 38707
(.branch 38663
(.branch 38641
(.leaf ⟨38622,19,(.group 8 595 false)⟩)
(.leaf ⟨38641,22,(.group 8 959 false)⟩))
(.branch 38685
(.leaf ⟨38663,22,(.group 8 958 false)⟩)
(.leaf ⟨38685,22,(.group 8 957 false)⟩)))
(.branch 38739
(.branch 38721
(.leaf ⟨38707,14,(.group 10 135 false)⟩)
(.leaf ⟨38721,18,(.group 9 437 false)⟩))
(.branch 38757
(.leaf ⟨38739,18,(.group 9 436 false)⟩)
(.leaf ⟨38757,18,(.group 9 435 false)⟩)))))))

theorem tree30_checked : tree30.check 37554 38775 = true := by decide +kernel

def tree31 : Tree := (.branch 39397
(.branch 39094
(.branch 38937
(.branch 38856
(.branch 38818
(.branch 38797
(.leaf ⟨38775,22,(.group 8 956 false)⟩)
(.leaf ⟨38797,21,(.group 8 821 false)⟩))
(.branch 38839
(.leaf ⟨38818,21,(.group 8 820 false)⟩)
(.leaf ⟨38839,17,(.group 9 357 false)⟩)))
(.branch 38895
(.branch 38875
(.leaf ⟨38856,19,(.group 8 594 false)⟩)
(.leaf ⟨38875,20,(.group 8 711 false)⟩))
(.branch 38915
(.leaf ⟨38895,20,(.group 8 710 false)⟩)
(.leaf ⟨38915,22,(.group 8 955 false)⟩))))
(.branch 39014
(.branch 38980
(.branch 38958
(.leaf ⟨38937,21,(.group 8 819 false)⟩)
(.leaf ⟨38958,22,(.group 8 954 false)⟩))
(.branch 38992
(.leaf ⟨38980,12,(.group 10 79 false)⟩)
(.leaf ⟨38992,22,(.group 8 953 false)⟩)))
(.branch 39057
(.branch 39035
(.leaf ⟨39014,21,(.group 8 818 false)⟩)
(.leaf ⟨39035,22,(.group 8 952 false)⟩))
(.branch 39075
(.leaf ⟨39057,18,(.group 9 434 false)⟩)
(.leaf ⟨39075,19,(.group 8 593 false)⟩)))))
(.branch 39250
(.branch 39168
(.branch 39127
(.branch 39111
(.leaf ⟨39094,17,(.group 9 356 false)⟩)
(.leaf ⟨39111,16,(.group 9 308 false)⟩))
(.branch 39147
(.leaf ⟨39127,20,(.group 8 709 false)⟩)
(.leaf ⟨39147,21,(.group 8 817 false)⟩)))
(.branch 39211
(.branch 39189
(.leaf ⟨39168,21,(.group 8 816 false)⟩)
(.leaf ⟨39189,22,(.group 8 951 false)⟩))
(.branch 39229
(.leaf ⟨39211,18,(.group 9 433 false)⟩)
(.leaf ⟨39229,21,(.group 8 815 false)⟩))))
(.branch 39325
(.branch 39290
(.branch 39268
(.leaf ⟨39250,18,(.group 9 432 false)⟩)
(.leaf ⟨39268,22,(.group 8 950 false)⟩))
(.branch 39304
(.leaf ⟨39290,14,(.group 10 134 false)⟩)
(.leaf ⟨39304,21,(.group 8 814 false)⟩)))
(.branch 39362
(.branch 39344
(.leaf ⟨39325,19,(.group 8 592 false)⟩)
(.leaf ⟨39344,18,(.group 9 431 false)⟩))
(.branch 39379
(.leaf ⟨39362,17,(.group 9 355 false)⟩)
(.leaf ⟨39379,18,(.group 9 430 false)⟩))))))
(.branch 39707
(.branch 39547
(.branch 39474
(.branch 39434
(.branch 39416
(.leaf ⟨39397,19,(.group 8 591 false)⟩)
(.leaf ⟨39416,18,(.group 9 429 false)⟩))
(.branch 39456
(.leaf ⟨39434,22,(.group 8 949 false)⟩)
(.leaf ⟨39456,18,(.group 9 428 false)⟩)))
(.branch 39506
(.branch 39491
(.leaf ⟨39474,17,(.group 9 354 false)⟩)
(.leaf ⟨39491,15,(.group 9 238 false)⟩))
(.branch 39528
(.leaf ⟨39506,22,(.group 8 948 false)⟩)
(.leaf ⟨39528,19,(.group 8 590 false)⟩))))
(.branch 39622
(.branch 39585
(.branch 39569
(.leaf ⟨39547,22,(.group 8 947 false)⟩)
(.leaf ⟨39569,16,(.group 9 307 false)⟩))
(.branch 39601
(.leaf ⟨39585,16,(.group 9 306 false)⟩)
(.leaf ⟨39601,21,(.group 8 813 false)⟩)))
(.branch 39666
(.branch 39644
(.leaf ⟨39622,22,(.group 8 946 false)⟩)
(.leaf ⟨39644,22,(.group 8 945 false)⟩))
(.branch 39688
(.leaf ⟨39666,22,(.group 8 944 false)⟩)
(.leaf ⟨39688,19,(.group 8 589 false)⟩)))))
(.branch 39870
(.branch 39788
(.branch 39748
(.branch 39727
(.leaf ⟨39707,20,(.group 8 708 false)⟩)
(.leaf ⟨39727,21,(.group 8 812 false)⟩))
(.branch 39768
(.leaf ⟨39748,20,(.group 8 707 false)⟩)
(.leaf ⟨39768,20,(.group 8 706 false)⟩)))
(.branch 39828
(.branch 39808
(.leaf ⟨39788,20,(.group 8 705 false)⟩)
(.leaf ⟨39808,20,(.group 8 704 false)⟩))
(.branch 39848
(.leaf ⟨39828,20,(.group 8 703 false)⟩)
(.leaf ⟨39848,22,(.group 8 943 false)⟩))))
(.branch 39937
(.branch 39899
(.branch 39884
(.leaf ⟨39870,14,(.group 10 133 false)⟩)
(.leaf ⟨39884,15,(.group 9 237 false)⟩))
(.branch 39918
(.leaf ⟨39899,19,(.group 8 588 false)⟩)
(.leaf ⟨39918,19,(.group 8 587 false)⟩)))
(.branch 39973
(.branch 39953
(.leaf ⟨39937,16,(.group 9 305 false)⟩)
(.leaf ⟨39953,20,(.group 8 702 false)⟩))
(.branch 39995
(.leaf ⟨39973,22,(.group 8 942 false)⟩)
(.leaf ⟨39995,15,(.group 9 236 false)⟩)))))))

theorem tree31_checked : tree31.check 38775 40010 = true := by decide +kernel

def tree32 : Tree := (.branch 40619
(.branch 40317
(.branch 40166
(.branch 40087
(.branch 40050
(.branch 40032
(.leaf ⟨40010,22,(.group 8 941 false)⟩)
(.leaf ⟨40032,18,(.group 9 427 false)⟩))
(.branch 40067
(.leaf ⟨40050,17,(.group 9 353 false)⟩)
(.leaf ⟨40067,20,(.group 8 701 false)⟩)))
(.branch 40126
(.branch 40106
(.leaf ⟨40087,19,(.group 8 586 false)⟩)
(.leaf ⟨40106,20,(.group 8 700 false)⟩))
(.branch 40144
(.leaf ⟨40126,18,(.group 9 426 false)⟩)
(.leaf ⟨40144,22,(.group 8 940 false)⟩))))
(.branch 40240
(.branch 40200
(.branch 40182
(.leaf ⟨40166,16,(.group 9 304 false)⟩)
(.leaf ⟨40182,18,(.group 9 425 false)⟩))
(.branch 40219
(.leaf ⟨40200,19,(.group 8 585 false)⟩)
(.leaf ⟨40219,21,(.group 8 811 false)⟩)))
(.branch 40276
(.branch 40254
(.leaf ⟨40240,14,(.group 10 132 false)⟩)
(.leaf ⟨40254,22,(.group 8 939 false)⟩))
(.branch 40295
(.leaf ⟨40276,19,(.group 8 584 false)⟩)
(.leaf ⟨40295,22,(.group 8 938 false)⟩)))))
(.branch 40460
(.branch 40382
(.branch 40351
(.branch 40337
(.leaf ⟨40317,20,(.group 8 699 false)⟩)
(.leaf ⟨40337,14,(.group 10 131 false)⟩))
(.branch 40365
(.leaf ⟨40351,14,(.group 10 130 false)⟩)
(.leaf ⟨40365,17,(.group 9 352 false)⟩)))
(.branch 40421
(.branch 40404
(.leaf ⟨40382,22,(.group 8 937 false)⟩)
(.leaf ⟨40404,17,(.group 9 351 false)⟩))
(.branch 40443
(.leaf ⟨40421,22,(.group 8 936 false)⟩)
(.leaf ⟨40443,17,(.group 9 350 false)⟩))))
(.branch 40543
(.branch 40500
(.branch 40479
(.leaf ⟨40460,19,(.group 8 583 false)⟩)
(.leaf ⟨40479,21,(.group 8 810 false)⟩))
(.branch 40522
(.leaf ⟨40500,22,(.group 8 935 false)⟩)
(.leaf ⟨40522,21,(.group 8 809 false)⟩)))
(.branch 40578
(.branch 40557
(.leaf ⟨40543,14,(.group 10 129 false)⟩)
(.leaf ⟨40557,21,(.group 8 808 false)⟩))
(.branch 40600
(.leaf ⟨40578,22,(.group 8 934 false)⟩)
(.leaf ⟨40600,19,(.group 8 582 false)⟩))))))
(.branch 40949
(.branch 40789
(.branch 40702
(.branch 40660
(.branch 40638
(.leaf ⟨40619,19,(.group 8 581 false)⟩)
(.leaf ⟨40638,22,(.group 8 933 false)⟩))
(.branch 40680
(.leaf ⟨40660,20,(.group 8 698 false)⟩)
(.leaf ⟨40680,22,(.group 8 932 false)⟩)))
(.branch 40746
(.branch 40724
(.leaf ⟨40702,22,(.group 8 931 false)⟩)
(.leaf ⟨40724,22,(.group 8 930 false)⟩))
(.branch 40767
(.leaf ⟨40746,21,(.group 8 807 false)⟩)
(.leaf ⟨40767,22,(.group 8 929 false)⟩))))
(.branch 40867
(.branch 40828
(.branch 40809
(.leaf ⟨40789,20,(.group 8 697 false)⟩)
(.leaf ⟨40809,19,(.group 8 580 false)⟩))
(.branch 40850
(.leaf ⟨40828,22,(.group 8 928 false)⟩)
(.leaf ⟨40850,17,(.group 9 349 false)⟩)))
(.branch 40907
(.branch 40889
(.leaf ⟨40867,22,(.group 8 927 false)⟩)
(.leaf ⟨40889,18,(.group 9 424 false)⟩))
(.branch 40927
(.leaf ⟨40907,20,(.group 8 696 false)⟩)
(.leaf ⟨40927,22,(.group 8 926 false)⟩)))))
(.branch 41102
(.branch 41020
(.branch 40985
(.branch 40971
(.leaf ⟨40949,22,(.group 8 925 false)⟩)
(.leaf ⟨40971,14,(.group 10 128 false)⟩))
(.branch 41002
(.leaf ⟨40985,17,(.group 9 348 false)⟩)
(.leaf ⟨41002,18,(.group 9 423 false)⟩)))
(.branch 41058
(.branch 41041
(.leaf ⟨41020,21,(.group 8 806 false)⟩)
(.leaf ⟨41041,17,(.group 9 347 false)⟩))
(.branch 41080
(.leaf ⟨41058,22,(.group 8 924 false)⟩)
(.leaf ⟨41080,22,(.group 8 923 false)⟩))))
(.branch 41175
(.branch 41138
(.branch 41116
(.leaf ⟨41102,14,(.group 10 127 false)⟩)
(.leaf ⟨41116,22,(.group 8 922 false)⟩))
(.branch 41153
(.leaf ⟨41138,15,(.group 9 235 false)⟩)
(.leaf ⟨41153,22,(.group 8 921 false)⟩)))
(.branch 41213
(.branch 41197
(.leaf ⟨41175,22,(.group 8 920 false)⟩)
(.leaf ⟨41197,16,(.group 9 303 false)⟩))
(.branch 41232
(.leaf ⟨41213,19,(.group 8 579 false)⟩)
(.leaf ⟨41232,15,(.group 9 234 false)⟩)))))))

theorem tree32_checked : tree32.check 40010 41247 = true := by decide +kernel

def tree33 : Tree := (.branch 41881
(.branch 41568
(.branch 41412
(.branch 41331
(.branch 41289
(.branch 41269
(.leaf ⟨41247,22,(.group 8 919 false)⟩)
(.leaf ⟨41269,20,(.group 8 695 false)⟩))
(.branch 41311
(.leaf ⟨41289,22,(.group 8 918 false)⟩)
(.leaf ⟨41311,20,(.group 8 694 false)⟩)))
(.branch 41374
(.branch 41352
(.leaf ⟨41331,21,(.group 8 805 false)⟩)
(.leaf ⟨41352,22,(.group 8 917 false)⟩))
(.branch 41391
(.leaf ⟨41374,17,(.group 9 346 false)⟩)
(.leaf ⟨41391,21,(.group 8 804 false)⟩))))
(.branch 41484
(.branch 41448
(.branch 41430
(.leaf ⟨41412,18,(.group 9 422 false)⟩)
(.leaf ⟨41430,18,(.group 9 421 false)⟩))
(.branch 41463
(.leaf ⟨41448,15,(.group 9 233 false)⟩)
(.leaf ⟨41463,21,(.group 8 803 false)⟩)))
(.branch 41524
(.branch 41506
(.leaf ⟨41484,22,(.group 8 916 false)⟩)
(.leaf ⟨41506,18,(.group 9 420 false)⟩))
(.branch 41546
(.leaf ⟨41524,22,(.group 8 915 false)⟩)
(.leaf ⟨41546,22,(.group 8 914 false)⟩)))))
(.branch 41735
(.branch 41652
(.branch 41610
(.branch 41590
(.leaf ⟨41568,22,(.group 8 913 false)⟩)
(.leaf ⟨41590,20,(.group 8 693 false)⟩))
(.branch 41632
(.leaf ⟨41610,22,(.group 8 912 false)⟩)
(.leaf ⟨41632,20,(.group 8 692 false)⟩)))
(.branch 41694
(.branch 41673
(.leaf ⟨41652,21,(.group 8 802 false)⟩)
(.leaf ⟨41673,21,(.group 8 801 false)⟩))
(.branch 41713
(.leaf ⟨41694,19,(.group 8 578 false)⟩)
(.leaf ⟨41713,22,(.group 8 911 false)⟩))))
(.branch 41811
(.branch 41770
(.branch 41756
(.leaf ⟨41735,21,(.group 8 800 false)⟩)
(.leaf ⟨41756,14,(.group 9 199 false)⟩))
(.branch 41792
(.leaf ⟨41770,22,(.group 8 910 false)⟩)
(.leaf ⟨41792,19,(.group 8 577 false)⟩)))
(.branch 41846
(.branch 41833
(.leaf ⟨41811,22,(.group 8 909 false)⟩)
(.leaf ⟨41833,13,(.group 10 102 false)⟩))
(.branch 41864
(.leaf ⟨41846,18,(.group 9 419 false)⟩)
(.leaf ⟨41864,17,(.group 9 345 false)⟩))))))
(.branch 42195
(.branch 42041
(.branch 41963
(.branch 41923
(.branch 41901
(.leaf ⟨41881,20,(.group 8 691 false)⟩)
(.leaf ⟨41901,22,(.group 8 908 false)⟩))
(.branch 41943
(.leaf ⟨41923,20,(.group 8 690 false)⟩)
(.leaf ⟨41943,20,(.group 8 689 false)⟩)))
(.branch 42003
(.branch 41983
(.leaf ⟨41963,20,(.group 8 688 false)⟩)
(.leaf ⟨41983,20,(.group 8 687 false)⟩))
(.branch 42021
(.leaf ⟨42003,18,(.group 9 418 false)⟩)
(.leaf ⟨42021,20,(.group 8 686 false)⟩))))
(.branch 42121
(.branch 42083
(.branch 42063
(.leaf ⟨42041,22,(.group 8 907 false)⟩)
(.leaf ⟨42063,20,(.group 8 685 false)⟩))
(.branch 42101
(.leaf ⟨42083,18,(.group 9 417 false)⟩)
(.leaf ⟨42101,20,(.group 8 684 false)⟩)))
(.branch 42155
(.branch 42135
(.leaf ⟨42121,14,(.group 9 198 false)⟩)
(.leaf ⟨42135,20,(.group 8 683 false)⟩))
(.branch 42176
(.leaf ⟨42155,21,(.group 8 799 false)⟩)
(.leaf ⟨42176,19,(.group 8 576 false)⟩)))))
(.branch 42347
(.branch 42271
(.branch 42234
(.branch 42212
(.leaf ⟨42195,17,(.group 9 344 false)⟩)
(.leaf ⟨42212,22,(.group 8 906 false)⟩))
(.branch 42249
(.leaf ⟨42234,15,(.group 9 232 false)⟩)
(.leaf ⟨42249,22,(.group 8 905 false)⟩)))
(.branch 42309
(.branch 42290
(.leaf ⟨42271,19,(.group 8 575 false)⟩)
(.leaf ⟨42290,19,(.group 8 574 false)⟩))
(.branch 42329
(.leaf ⟨42309,20,(.group 8 682 false)⟩)
(.leaf ⟨42329,18,(.group 9 416 false)⟩))))
(.branch 42429
(.branch 42389
(.branch 42369
(.leaf ⟨42347,22,(.group 8 904 false)⟩)
(.leaf ⟨42369,20,(.group 8 681 false)⟩))
(.branch 42411
(.leaf ⟨42389,22,(.group 8 903 false)⟩)
(.leaf ⟨42411,18,(.group 9 415 false)⟩)))
(.branch 42473
(.branch 42451
(.leaf ⟨42429,22,(.group 8 902 false)⟩)
(.leaf ⟨42451,22,(.group 8 901 false)⟩))
(.branch 42491
(.leaf ⟨42473,18,(.group 9 414 false)⟩)
(.leaf ⟨42491,18,(.group 9 413 false)⟩)))))))

theorem tree33_checked : tree33.check 41247 42509 = true := by decide +kernel

def tree34 : Tree := (.branch 43119
(.branch 42816
(.branch 42651
(.branch 42578
(.branch 42542
(.branch 42528
(.leaf ⟨42509,19,(.group 8 573 false)⟩)
(.leaf ⟨42528,14,(.group 9 197 false)⟩))
(.branch 42557
(.leaf ⟨42542,15,(.group 9 231 false)⟩)
(.leaf ⟨42557,21,(.group 8 798 false)⟩)))
(.branch 42607
(.branch 42586
(.leaf ⟨42578,8,(.group 10 23 false)⟩)
(.leaf ⟨42586,21,(.group 8 797 false)⟩))
(.branch 42629
(.leaf ⟨42607,22,(.group 8 900 false)⟩)
(.leaf ⟨42629,22,(.group 8 899 false)⟩))))
(.branch 42735
(.branch 42694
(.branch 42672
(.leaf ⟨42651,21,(.group 8 796 false)⟩)
(.leaf ⟨42672,22,(.group 8 898 false)⟩))
(.branch 42714
(.leaf ⟨42694,20,(.group 8 680 false)⟩)
(.leaf ⟨42714,21,(.group 8 795 false)⟩)))
(.branch 42775
(.branch 42756
(.leaf ⟨42735,21,(.group 8 794 false)⟩)
(.leaf ⟨42756,19,(.group 8 572 false)⟩))
(.branch 42797
(.leaf ⟨42775,22,(.group 8 897 false)⟩)
(.leaf ⟨42797,19,(.group 8 571 false)⟩)))))
(.branch 42967
(.branch 42896
(.branch 42858
(.branch 42837
(.leaf ⟨42816,21,(.group 8 793 false)⟩)
(.leaf ⟨42837,21,(.group 8 792 false)⟩))
(.branch 42880
(.leaf ⟨42858,22,(.group 8 896 false)⟩)
(.leaf ⟨42880,16,(.group 9 302 false)⟩)))
(.branch 42926
(.branch 42913
(.leaf ⟨42896,17,(.group 9 343 false)⟩)
(.leaf ⟨42913,13,(.group 10 101 false)⟩))
(.branch 42947
(.leaf ⟨42926,21,(.group 8 791 false)⟩)
(.leaf ⟨42947,20,(.group 8 679 false)⟩))))
(.branch 43043
(.branch 43008
(.branch 42988
(.leaf ⟨42967,21,(.group 8 790 false)⟩)
(.leaf ⟨42988,20,(.group 8 678 false)⟩))
(.branch 43025
(.leaf ⟨43008,17,(.group 9 342 false)⟩)
(.leaf ⟨43025,18,(.group 9 412 false)⟩)))
(.branch 43084
(.branch 43063
(.leaf ⟨43043,20,(.group 8 677 false)⟩)
(.leaf ⟨43063,21,(.group 8 789 false)⟩))
(.branch 43102
(.leaf ⟨43084,18,(.group 9 411 false)⟩)
(.leaf ⟨43102,17,(.group 9 341 false)⟩))))))
(.branch 43433
(.branch 43282
(.branch 43201
(.branch 43157
(.branch 43135
(.leaf ⟨43119,16,(.group 9 301 false)⟩)
(.leaf ⟨43135,22,(.group 8 895 false)⟩))
(.branch 43179
(.leaf ⟨43157,22,(.group 8 894 false)⟩)
(.leaf ⟨43179,22,(.group 8 893 false)⟩)))
(.branch 43239
(.branch 43219
(.leaf ⟨43201,18,(.group 9 410 false)⟩)
(.leaf ⟨43219,20,(.group 8 676 false)⟩))
(.branch 43260
(.leaf ⟨43239,21,(.group 8 788 false)⟩)
(.leaf ⟨43260,22,(.group 8 892 false)⟩))))
(.branch 43360
(.branch 43323
(.branch 43302
(.leaf ⟨43282,20,(.group 8 675 false)⟩)
(.leaf ⟨43302,21,(.group 8 787 false)⟩))
(.branch 43341
(.leaf ⟨43323,18,(.group 9 409 false)⟩)
(.leaf ⟨43341,19,(.group 8 570 false)⟩)))
(.branch 43398
(.branch 43376
(.leaf ⟨43360,16,(.group 9 300 false)⟩)
(.leaf ⟨43376,22,(.group 8 891 false)⟩))
(.branch 43416
(.leaf ⟨43398,18,(.group 9 408 false)⟩)
(.leaf ⟨43416,17,(.group 9 340 false)⟩)))))
(.branch 43592
(.branch 43517
(.branch 43475
(.branch 43454
(.leaf ⟨43433,21,(.group 8 786 false)⟩)
(.leaf ⟨43454,21,(.group 8 785 false)⟩))
(.branch 43497
(.leaf ⟨43475,22,(.group 8 890 false)⟩)
(.leaf ⟨43497,20,(.group 8 674 false)⟩)))
(.branch 43558
(.branch 43538
(.leaf ⟨43517,21,(.group 8 784 false)⟩)
(.leaf ⟨43538,20,(.group 8 673 false)⟩))
(.branch 43579
(.leaf ⟨43558,21,(.group 8 783 false)⟩)
(.leaf ⟨43579,13,(.group 10 100 false)⟩))))
(.branch 43674
(.branch 43635
(.branch 43614
(.leaf ⟨43592,22,(.group 8 889 false)⟩)
(.leaf ⟨43614,21,(.group 8 782 false)⟩))
(.branch 43655
(.leaf ⟨43635,20,(.group 8 672 false)⟩)
(.leaf ⟨43655,19,(.group 8 569 false)⟩)))
(.branch 43707
(.branch 43689
(.leaf ⟨43674,15,(.group 9 230 false)⟩)
(.leaf ⟨43689,18,(.group 9 407 false)⟩))
(.branch 43728
(.leaf ⟨43707,21,(.group 8 781 false)⟩)
(.leaf ⟨43728,18,(.group 9 406 false)⟩)))))))

theorem tree34_checked : tree34.check 42509 43746 = true := by decide +kernel

def tree35 : Tree := (.branch 44360
(.branch 44062
(.branch 43898
(.branch 43819
(.branch 43786
(.branch 43768
(.leaf ⟨43746,22,(.group 8 888 false)⟩)
(.leaf ⟨43768,18,(.group 9 405 false)⟩))
(.branch 43808
(.leaf ⟨43786,22,(.group 8 887 false)⟩)
(.leaf ⟨43808,11,(.group 10 54 false)⟩)))
(.branch 43858
(.branch 43840
(.leaf ⟨43819,21,(.group 8 780 false)⟩)
(.leaf ⟨43840,18,(.group 9 404 false)⟩))
(.branch 43876
(.leaf ⟨43858,18,(.group 9 403 false)⟩)
(.leaf ⟨43876,22,(.group 8 886 false)⟩))))
(.branch 43981
(.branch 43938
(.branch 43916
(.leaf ⟨43898,18,(.group 8 491 false)⟩)
(.leaf ⟨43916,22,(.group 8 885 false)⟩))
(.branch 43959
(.leaf ⟨43938,21,(.group 8 779 false)⟩)
(.leaf ⟨43959,22,(.group 8 884 false)⟩)))
(.branch 44022
(.branch 44002
(.leaf ⟨43981,21,(.group 8 778 false)⟩)
(.leaf ⟨44002,20,(.group 8 671 false)⟩))
(.branch 44041
(.leaf ⟨44022,19,(.group 8 568 false)⟩)
(.leaf ⟨44041,21,(.group 8 777 false)⟩)))))
(.branch 44219
(.branch 44140
(.branch 44103
(.branch 44082
(.leaf ⟨44062,20,(.group 8 670 false)⟩)
(.leaf ⟨44082,21,(.group 8 776 false)⟩))
(.branch 44118
(.leaf ⟨44103,15,(.group 9 229 false)⟩)
(.leaf ⟨44118,22,(.group 8 883 false)⟩)))
(.branch 44177
(.branch 44157
(.leaf ⟨44140,17,(.group 9 339 false)⟩)
(.leaf ⟨44157,20,(.group 8 669 false)⟩))
(.branch 44199
(.leaf ⟨44177,22,(.group 8 882 false)⟩)
(.leaf ⟨44199,20,(.group 8 668 false)⟩))))
(.branch 44295
(.branch 44257
(.branch 44238
(.leaf ⟨44219,19,(.group 8 567 false)⟩)
(.leaf ⟨44238,19,(.group 8 566 false)⟩))
(.branch 44275
(.leaf ⟨44257,18,(.group 8 490 false)⟩)
(.leaf ⟨44275,20,(.group 8 667 false)⟩)))
(.branch 44330
(.branch 44310
(.leaf ⟨44295,15,(.group 9 228 false)⟩)
(.leaf ⟨44310,20,(.group 8 666 false)⟩))
(.branch 44351
(.leaf ⟨44330,21,(.group 8 775 false)⟩)
(.leaf ⟨44351,9,(.group 10 37 false)⟩))))))
(.branch 44673
(.branch 44519
(.branch 44440
(.branch 44400
(.branch 44380
(.leaf ⟨44360,20,(.group 8 665 false)⟩)
(.leaf ⟨44380,20,(.group 8 664 false)⟩))
(.branch 44419
(.leaf ⟨44400,19,(.group 8 565 false)⟩)
(.leaf ⟨44419,21,(.group 8 774 false)⟩)))
(.branch 44481
(.branch 44459
(.leaf ⟨44440,19,(.group 8 564 false)⟩)
(.leaf ⟨44459,22,(.group 8 881 false)⟩))
(.branch 44502
(.leaf ⟨44481,21,(.group 8 773 false)⟩)
(.leaf ⟨44502,17,(.group 9 338 false)⟩))))
(.branch 44595
(.branch 44557
(.branch 44536
(.leaf ⟨44519,17,(.group 9 337 false)⟩)
(.leaf ⟨44536,21,(.group 8 772 false)⟩))
(.branch 44573
(.leaf ⟨44557,16,(.group 9 299 false)⟩)
(.leaf ⟨44573,22,(.group 8 880 false)⟩)))
(.branch 44636
(.branch 44614
(.leaf ⟨44595,19,(.group 8 563 false)⟩)
(.leaf ⟨44614,22,(.group 8 879 false)⟩))
(.branch 44651
(.leaf ⟨44636,15,(.group 9 227 false)⟩)
(.leaf ⟨44651,22,(.group 8 878 false)⟩)))))
(.branch 44816
(.branch 44749
(.branch 44707
(.branch 44691
(.leaf ⟨44673,18,(.group 8 489 false)⟩)
(.leaf ⟨44691,16,(.group 9 298 false)⟩))
(.branch 44728
(.leaf ⟨44707,21,(.group 8 771 false)⟩)
(.leaf ⟨44728,21,(.group 8 770 false)⟩)))
(.branch 44784
(.branch 44770
(.leaf ⟨44749,21,(.group 8 769 false)⟩)
(.leaf ⟨44770,14,(.group 9 196 false)⟩))
(.branch 44798
(.leaf ⟨44784,14,(.group 9 195 false)⟩)
(.leaf ⟨44798,18,(.group 8 488 false)⟩))))
(.branch 44892
(.branch 44855
(.branch 44837
(.leaf ⟨44816,21,(.group 8 768 false)⟩)
(.leaf ⟨44837,18,(.group 8 487 false)⟩))
(.branch 44872
(.leaf ⟨44855,17,(.group 9 336 false)⟩)
(.leaf ⟨44872,20,(.group 8 663 false)⟩)))
(.branch 44933
(.branch 44912
(.leaf ⟨44892,20,(.group 8 662 false)⟩)
(.leaf ⟨44912,21,(.group 8 767 false)⟩))
(.branch 44953
(.leaf ⟨44933,20,(.group 8 661 false)⟩)
(.leaf ⟨44953,19,(.group 8 562 false)⟩)))))))

theorem tree35_checked : tree35.check 43746 44972 = true := by decide +kernel

def tree36 : Tree := (.branch 45600
(.branch 45295
(.branch 45140
(.branch 45058
(.branch 45014
(.branch 44994
(.leaf ⟨44972,22,(.group 8 877 false)⟩)
(.leaf ⟨44994,20,(.group 8 660 false)⟩))
(.branch 45036
(.leaf ⟨45014,22,(.group 8 876 false)⟩)
(.leaf ⟨45036,22,(.group 8 875 false)⟩)))
(.branch 45098
(.branch 45076
(.leaf ⟨45058,18,(.group 8 486 false)⟩)
(.leaf ⟨45076,22,(.group 8 874 false)⟩))
(.branch 45119
(.leaf ⟨45098,21,(.group 8 766 false)⟩)
(.leaf ⟨45119,21,(.group 8 765 false)⟩))))
(.branch 45224
(.branch 45182
(.branch 45162
(.leaf ⟨45140,22,(.group 8 873 false)⟩)
(.leaf ⟨45162,20,(.group 8 659 false)⟩))
(.branch 45204
(.leaf ⟨45182,22,(.group 8 872 false)⟩)
(.leaf ⟨45204,20,(.group 8 658 false)⟩)))
(.branch 45257
(.branch 45242
(.leaf ⟨45224,18,(.group 8 485 false)⟩)
(.leaf ⟨45242,15,(.group 9 226 false)⟩))
(.branch 45275
(.leaf ⟨45257,18,(.group 8 484 false)⟩)
(.leaf ⟨45275,20,(.group 8 657 false)⟩)))))
(.branch 45448
(.branch 45372
(.branch 45338
(.branch 45317
(.leaf ⟨45295,22,(.group 8 871 false)⟩)
(.leaf ⟨45317,21,(.group 8 764 false)⟩))
(.branch 45355
(.leaf ⟨45338,17,(.group 9 335 false)⟩)
(.leaf ⟨45355,17,(.group 9 334 false)⟩)))
(.branch 45405
(.branch 45386
(.leaf ⟨45372,14,(.group 9 194 false)⟩)
(.leaf ⟨45386,19,(.group 8 561 false)⟩))
(.branch 45427
(.leaf ⟨45405,22,(.group 8 870 false)⟩)
(.leaf ⟨45427,21,(.group 8 763 false)⟩))))
(.branch 45523
(.branch 45490
(.branch 45468
(.leaf ⟨45448,20,(.group 8 656 false)⟩)
(.leaf ⟨45468,22,(.group 8 869 false)⟩))
(.branch 45506
(.leaf ⟨45490,16,(.group 9 297 false)⟩)
(.leaf ⟨45506,17,(.group 9 333 false)⟩)))
(.branch 45563
(.branch 45544
(.leaf ⟨45523,21,(.group 8 762 false)⟩)
(.leaf ⟨45544,19,(.group 8 560 false)⟩))
(.branch 45585
(.leaf ⟨45563,22,(.group 8 868 false)⟩)
(.leaf ⟨45585,15,(.group 9 225 false)⟩))))))
(.branch 45890
(.branch 45752
(.branch 45677
(.branch 45639
(.branch 45622
(.leaf ⟨45600,22,(.group 8 867 false)⟩)
(.leaf ⟨45622,17,(.group 9 332 false)⟩))
(.branch 45657
(.leaf ⟨45639,18,(.group 8 483 false)⟩)
(.leaf ⟨45657,20,(.group 8 655 false)⟩)))
(.branch 45713
(.branch 45698
(.leaf ⟨45677,21,(.group 8 761 false)⟩)
(.leaf ⟨45698,15,(.group 9 224 false)⟩))
(.branch 45731
(.leaf ⟨45713,18,(.group 8 482 false)⟩)
(.leaf ⟨45731,21,(.group 8 760 false)⟩))))
(.branch 45821
(.branch 45787
(.branch 45766
(.leaf ⟨45752,14,(.group 9 193 false)⟩)
(.leaf ⟨45766,21,(.group 8 759 false)⟩))
(.branch 45804
(.leaf ⟨45787,17,(.group 9 331 false)⟩)
(.leaf ⟨45804,17,(.group 9 330 false)⟩)))
(.branch 45861
(.branch 45839
(.leaf ⟨45821,18,(.group 8 481 false)⟩)
(.leaf ⟨45839,22,(.group 8 866 false)⟩))
(.branch 45879
(.leaf ⟨45861,18,(.group 8 480 false)⟩)
(.leaf ⟨45879,11,(.group 10 53 false)⟩)))))
(.branch 46039
(.branch 45965
(.branch 45926
(.branch 45907
(.leaf ⟨45890,17,(.group 9 329 false)⟩)
(.leaf ⟨45907,19,(.group 8 559 false)⟩))
(.branch 45946
(.leaf ⟨45926,20,(.group 8 654 false)⟩)
(.leaf ⟨45946,19,(.group 8 558 false)⟩)))
(.branch 45997
(.branch 45975
(.leaf ⟨45965,10,(.group 10 42 false)⟩)
(.leaf ⟨45975,22,(.group 7 845 false)⟩))
(.branch 46017
(.leaf ⟨45997,20,(.group 8 653 false)⟩)
(.leaf ⟨46017,22,(.group 7 844 false)⟩))))
(.branch 46115
(.branch 46075
(.branch 46057
(.leaf ⟨46039,18,(.group 8 479 false)⟩)
(.leaf ⟨46057,18,(.group 8 478 false)⟩))
(.branch 46095
(.leaf ⟨46075,20,(.group 8 652 false)⟩)
(.leaf ⟨46095,20,(.group 8 651 false)⟩)))
(.branch 46156
(.branch 46134
(.leaf ⟨46115,19,(.group 8 557 false)⟩)
(.leaf ⟨46134,22,(.group 7 843 false)⟩))
(.branch 46177
(.leaf ⟨46156,21,(.group 8 758 false)⟩)
(.leaf ⟨46177,13,(.group 10 99 false)⟩)))))))

theorem tree36_checked : tree36.check 44972 46190 = true := by decide +kernel

def tree37 : Tree := (.branch 46820
(.branch 46498
(.branch 46347
(.branch 46271
(.branch 46232
(.branch 46211
(.leaf ⟨46190,21,(.group 8 757 false)⟩)
(.leaf ⟨46211,21,(.group 8 756 false)⟩))
(.branch 46252
(.leaf ⟨46232,20,(.group 8 650 false)⟩)
(.leaf ⟨46252,19,(.group 8 556 false)⟩)))
(.branch 46308
(.branch 46289
(.leaf ⟨46271,18,(.group 8 477 false)⟩)
(.leaf ⟨46289,19,(.group 8 555 false)⟩))
(.branch 46329
(.leaf ⟨46308,21,(.group 8 755 false)⟩)
(.leaf ⟨46329,18,(.group 8 476 false)⟩))))
(.branch 46417
(.branch 46381
(.branch 46366
(.leaf ⟨46347,19,(.group 8 554 false)⟩)
(.leaf ⟨46366,15,(.group 9 223 false)⟩))
(.branch 46403
(.leaf ⟨46381,22,(.group 7 842 false)⟩)
(.leaf ⟨46403,14,(.group 9 192 false)⟩)))
(.branch 46460
(.branch 46438
(.leaf ⟨46417,21,(.group 8 754 false)⟩)
(.leaf ⟨46438,22,(.group 7 841 false)⟩))
(.branch 46480
(.leaf ⟨46460,20,(.group 8 649 false)⟩)
(.leaf ⟨46480,18,(.group 8 475 false)⟩)))))
(.branch 46656
(.branch 46574
(.branch 46534
(.branch 46516
(.leaf ⟨46498,18,(.group 8 474 false)⟩)
(.leaf ⟨46516,18,(.group 8 473 false)⟩))
(.branch 46554
(.leaf ⟨46534,20,(.group 8 648 false)⟩)
(.leaf ⟨46554,20,(.group 8 647 false)⟩)))
(.branch 46615
(.branch 46594
(.leaf ⟨46574,20,(.group 8 646 false)⟩)
(.leaf ⟨46594,21,(.group 8 753 false)⟩))
(.branch 46635
(.leaf ⟨46615,20,(.group 8 645 false)⟩)
(.leaf ⟨46635,21,(.group 8 752 false)⟩))))
(.branch 46738
(.branch 46696
(.branch 46677
(.leaf ⟨46656,21,(.group 8 751 false)⟩)
(.leaf ⟨46677,19,(.group 8 553 false)⟩))
(.branch 46718
(.leaf ⟨46696,22,(.group 7 840 false)⟩)
(.leaf ⟨46718,20,(.group 8 644 false)⟩)))
(.branch 46781
(.branch 46759
(.leaf ⟨46738,21,(.group 8 750 false)⟩)
(.leaf ⟨46759,22,(.group 7 839 false)⟩))
(.branch 46801
(.leaf ⟨46781,20,(.group 8 643 false)⟩)
(.leaf ⟨46801,19,(.group 8 552 false)⟩))))))
(.branch 47133
(.branch 46975
(.branch 46899
(.branch 46864
(.branch 46842
(.leaf ⟨46820,22,(.group 7 838 false)⟩)
(.leaf ⟨46842,22,(.group 7 837 false)⟩))
(.branch 46881
(.leaf ⟨46864,17,(.group 9 328 false)⟩)
(.leaf ⟨46881,18,(.group 8 472 false)⟩)))
(.branch 46935
(.branch 46918
(.leaf ⟨46899,19,(.group 8 551 false)⟩)
(.leaf ⟨46918,17,(.group 9 327 false)⟩))
(.branch 46955
(.leaf ⟨46935,20,(.group 8 642 false)⟩)
(.leaf ⟨46955,20,(.group 8 641 false)⟩))))
(.branch 47053
(.branch 47012
(.branch 46992
(.leaf ⟨46975,17,(.group 9 326 false)⟩)
(.leaf ⟨46992,20,(.group 8 640 false)⟩))
(.branch 47032
(.leaf ⟨47012,20,(.group 8 639 false)⟩)
(.leaf ⟨47032,21,(.group 8 749 false)⟩)))
(.branch 47093
(.branch 47073
(.leaf ⟨47053,20,(.group 8 638 false)⟩)
(.leaf ⟨47073,20,(.group 8 637 false)⟩))
(.branch 47113
(.leaf ⟨47093,20,(.group 8 636 false)⟩)
(.leaf ⟨47113,20,(.group 8 635 false)⟩)))))
(.branch 47301
(.branch 47218
(.branch 47174
(.branch 47154
(.leaf ⟨47133,21,(.group 8 748 false)⟩)
(.leaf ⟨47154,20,(.group 8 634 false)⟩))
(.branch 47196
(.leaf ⟨47174,22,(.group 7 836 false)⟩)
(.leaf ⟨47196,22,(.group 7 835 false)⟩)))
(.branch 47258
(.branch 47240
(.leaf ⟨47218,22,(.group 7 834 false)⟩)
(.leaf ⟨47240,18,(.group 8 471 false)⟩))
(.branch 47280
(.leaf ⟨47258,22,(.group 7 833 false)⟩)
(.leaf ⟨47280,21,(.group 8 747 false)⟩))))
(.branch 47373
(.branch 47342
(.branch 47322
(.leaf ⟨47301,21,(.group 8 746 false)⟩)
(.leaf ⟨47322,20,(.group 8 633 false)⟩))
(.branch 47360
(.leaf ⟨47342,18,(.group 8 470 false)⟩)
(.leaf ⟨47360,13,(.group 9 154 false)⟩)))
(.branch 47411
(.branch 47392
(.leaf ⟨47373,19,(.group 8 550 false)⟩)
(.leaf ⟨47392,19,(.group 8 549 false)⟩))
(.branch 47433
(.leaf ⟨47411,22,(.group 7 832 false)⟩)
(.leaf ⟨47433,22,(.group 7 831 false)⟩)))))))

theorem tree37_checked : tree37.check 46190 47455 = true := by decide +kernel

def tree38 : Tree := (.branch 48086
(.branch 47785
(.branch 47623
(.branch 47537
(.branch 47497
(.branch 47476
(.leaf ⟨47455,21,(.group 8 745 false)⟩)
(.leaf ⟨47476,21,(.group 8 744 false)⟩))
(.branch 47518
(.leaf ⟨47497,21,(.group 8 743 false)⟩)
(.leaf ⟨47518,19,(.group 8 548 false)⟩)))
(.branch 47581
(.branch 47559
(.leaf ⟨47537,22,(.group 7 830 false)⟩)
(.leaf ⟨47559,22,(.group 7 829 false)⟩))
(.branch 47603
(.leaf ⟨47581,22,(.group 7 828 false)⟩)
(.leaf ⟨47603,20,(.group 8 632 false)⟩))))
(.branch 47700
(.branch 47667
(.branch 47645
(.leaf ⟨47623,22,(.group 7 827 false)⟩)
(.leaf ⟨47645,22,(.group 7 826 false)⟩))
(.branch 47681
(.leaf ⟨47667,14,(.group 9 191 false)⟩)
(.leaf ⟨47681,19,(.group 8 547 false)⟩)))
(.branch 47742
(.branch 47722
(.leaf ⟨47700,22,(.group 7 825 false)⟩)
(.leaf ⟨47722,20,(.group 8 631 false)⟩))
(.branch 47763
(.leaf ⟨47742,21,(.group 8 742 false)⟩)
(.leaf ⟨47763,22,(.group 7 824 false)⟩)))))
(.branch 47940
(.branch 47856
(.branch 47820
(.branch 47802
(.leaf ⟨47785,17,(.group 9 325 false)⟩)
(.leaf ⟨47802,18,(.group 8 469 false)⟩))
(.branch 47835
(.leaf ⟨47820,15,(.group 9 222 false)⟩)
(.leaf ⟨47835,21,(.group 8 741 false)⟩)))
(.branch 47899
(.branch 47878
(.leaf ⟨47856,22,(.group 7 823 false)⟩)
(.leaf ⟨47878,21,(.group 8 740 false)⟩))
(.branch 47919
(.leaf ⟨47899,20,(.group 8 630 false)⟩)
(.leaf ⟨47919,21,(.group 8 739 false)⟩))))
(.branch 48015
(.branch 47978
(.branch 47960
(.leaf ⟨47940,20,(.group 8 629 false)⟩)
(.leaf ⟨47960,18,(.group 8 468 false)⟩))
(.branch 47998
(.leaf ⟨47978,20,(.group 8 628 false)⟩)
(.leaf ⟨47998,17,(.group 8 400 false)⟩)))
(.branch 48055
(.branch 48034
(.leaf ⟨48015,19,(.group 8 546 false)⟩)
(.leaf ⟨48034,21,(.group 8 738 false)⟩))
(.branch 48068
(.leaf ⟨48055,13,(.group 9 153 false)⟩)
(.leaf ⟨48068,18,(.group 8 467 false)⟩))))))
(.branch 48395
(.branch 48241
(.branch 48167
(.branch 48124
(.branch 48106
(.leaf ⟨48086,20,(.group 8 627 false)⟩)
(.leaf ⟨48106,18,(.group 8 466 false)⟩))
(.branch 48145
(.leaf ⟨48124,21,(.group 8 737 false)⟩)
(.leaf ⟨48145,22,(.group 7 822 false)⟩)))
(.branch 48206
(.branch 48185
(.leaf ⟨48167,18,(.group 8 465 false)⟩)
(.leaf ⟨48185,21,(.group 8 736 false)⟩))
(.branch 48223
(.leaf ⟨48206,17,(.group 8 399 false)⟩)
(.leaf ⟨48223,18,(.group 8 464 false)⟩))))
(.branch 48318
(.branch 48281
(.branch 48259
(.leaf ⟨48241,18,(.group 8 463 false)⟩)
(.leaf ⟨48259,22,(.group 7 821 false)⟩))
(.branch 48296
(.leaf ⟨48281,15,(.group 9 221 false)⟩)
(.leaf ⟨48296,22,(.group 7 820 false)⟩)))
(.branch 48356
(.branch 48334
(.leaf ⟨48318,16,(.group 9 296 false)⟩)
(.leaf ⟨48334,22,(.group 7 819 false)⟩))
(.branch 48373
(.leaf ⟨48356,17,(.group 8 398 false)⟩)
(.leaf ⟨48373,22,(.group 7 818 false)⟩)))))
(.branch 48547
(.branch 48468
(.branch 48426
(.branch 48406
(.leaf ⟨48395,11,(.group 10 52 false)⟩)
(.leaf ⟨48406,20,(.group 8 626 false)⟩))
(.branch 48446
(.leaf ⟨48426,20,(.group 8 625 false)⟩)
(.leaf ⟨48446,22,(.group 7 817 false)⟩)))
(.branch 48505
(.branch 48486
(.leaf ⟨48468,18,(.group 8 462 false)⟩)
(.leaf ⟨48486,19,(.group 8 545 false)⟩))
(.branch 48525
(.leaf ⟨48505,20,(.group 8 624 false)⟩)
(.leaf ⟨48525,22,(.group 7 816 false)⟩))))
(.branch 48623
(.branch 48586
(.branch 48565
(.leaf ⟨48547,18,(.group 8 461 false)⟩)
(.leaf ⟨48565,21,(.group 8 735 false)⟩))
(.branch 48605
(.leaf ⟨48586,19,(.group 8 544 false)⟩)
(.leaf ⟨48605,18,(.group 8 460 false)⟩)))
(.branch 48661
(.branch 48640
(.leaf ⟨48623,17,(.group 8 397 false)⟩)
(.leaf ⟨48640,21,(.group 8 734 false)⟩))
(.branch 48680
(.leaf ⟨48661,19,(.group 8 543 false)⟩)
(.leaf ⟨48680,17,(.group 8 396 false)⟩)))))))

theorem tree38_checked : tree38.check 47455 48697 = true := by decide +kernel

def tree39 : Tree := (.branch 48967
(.branch 48855
(.branch 48799
(.branch 48771
(.branch 48740
(.branch 48718
(.leaf ⟨48697,21,(.group 8 733 false)⟩)
(.leaf ⟨48718,22,(.group 7 815 false)⟩))
(.branch 48757
(.leaf ⟨48740,17,(.group 8 395 false)⟩)
(.leaf ⟨48757,14,(.group 8 202 false)⟩)))
(.branch 48785
(.branch 48778
(.leaf ⟨48771,7,(.group 0 0 false)⟩)
(.leaf ⟨48778,7,(.group 0 1 false)⟩))
(.branch 48792
(.leaf ⟨48785,7,(.group 0 2 false)⟩)
(.leaf ⟨48792,7,(.group 0 3 false)⟩))))
(.branch 48827
(.branch 48813
(.branch 48806
(.leaf ⟨48799,7,(.group 0 4 false)⟩)
(.leaf ⟨48806,7,(.group 0 5 false)⟩))
(.branch 48820
(.leaf ⟨48813,7,(.group 1 0 false)⟩)
(.leaf ⟨48820,7,(.group 2 0 false)⟩)))
(.branch 48841
(.branch 48834
(.leaf ⟨48827,7,(.group 3 0 false)⟩)
(.leaf ⟨48834,7,(.group 4 0 false)⟩))
(.branch 48848
(.leaf ⟨48841,7,(.group 5 0 false)⟩)
(.leaf ⟨48848,7,(.group 5 1 false)⟩)))))
(.branch 48911
(.branch 48883
(.branch 48869
(.branch 48862
(.leaf ⟨48855,7,(.group 5 2 false)⟩)
(.leaf ⟨48862,7,(.group 5 3 false)⟩))
(.branch 48876
(.leaf ⟨48869,7,(.group 5 4 false)⟩)
(.leaf ⟨48876,7,(.group 5 5 false)⟩)))
(.branch 48897
(.branch 48890
(.leaf ⟨48883,7,(.group 5 6 false)⟩)
(.leaf ⟨48890,7,(.group 5 7 false)⟩))
(.branch 48904
(.leaf ⟨48897,7,(.group 5 8 false)⟩)
(.leaf ⟨48904,7,(.group 5 9 false)⟩))))
(.branch 48939
(.branch 48925
(.branch 48918
(.leaf ⟨48911,7,(.group 5 10 false)⟩)
(.leaf ⟨48918,7,(.group 5 11 false)⟩))
(.branch 48932
(.leaf ⟨48925,7,(.group 5 12 false)⟩)
(.leaf ⟨48932,7,(.group 5 13 false)⟩)))
(.branch 48953
(.branch 48946
(.leaf ⟨48939,7,(.group 5 14 false)⟩)
(.leaf ⟨48946,7,(.group 5 15 false)⟩))
(.branch 48960
(.leaf ⟨48953,7,(.group 5 16 false)⟩)
(.leaf ⟨48960,7,(.group 5 17 false)⟩))))))
(.branch 49079
(.branch 49023
(.branch 48995
(.branch 48981
(.branch 48974
(.leaf ⟨48967,7,(.group 5 18 false)⟩)
(.leaf ⟨48974,7,(.group 5 19 false)⟩))
(.branch 48988
(.leaf ⟨48981,7,(.group 5 20 false)⟩)
(.leaf ⟨48988,7,(.group 5 21 false)⟩)))
(.branch 49009
(.branch 49002
(.leaf ⟨48995,7,(.group 5 22 false)⟩)
(.leaf ⟨49002,7,(.group 5 23 false)⟩))
(.branch 49016
(.leaf ⟨49009,7,(.group 5 24 false)⟩)
(.leaf ⟨49016,7,(.group 5 25 false)⟩))))
(.branch 49051
(.branch 49037
(.branch 49030
(.leaf ⟨49023,7,(.group 5 26 false)⟩)
(.leaf ⟨49030,7,(.group 5 27 false)⟩))
(.branch 49044
(.leaf ⟨49037,7,(.group 5 28 false)⟩)
(.leaf ⟨49044,7,(.group 5 29 false)⟩)))
(.branch 49065
(.branch 49058
(.leaf ⟨49051,7,(.group 5 30 false)⟩)
(.leaf ⟨49058,7,(.group 5 31 false)⟩))
(.branch 49072
(.leaf ⟨49065,7,(.group 5 32 false)⟩)
(.leaf ⟨49072,7,(.group 5 33 false)⟩)))))
(.branch 49135
(.branch 49107
(.branch 49093
(.branch 49086
(.leaf ⟨49079,7,(.group 5 34 false)⟩)
(.leaf ⟨49086,7,(.group 5 35 false)⟩))
(.branch 49100
(.leaf ⟨49093,7,(.group 5 36 false)⟩)
(.leaf ⟨49100,7,(.group 5 37 false)⟩)))
(.branch 49121
(.branch 49114
(.leaf ⟨49107,7,(.group 5 38 false)⟩)
(.leaf ⟨49114,7,(.group 5 39 false)⟩))
(.branch 49128
(.leaf ⟨49121,7,(.group 5 40 false)⟩)
(.leaf ⟨49128,7,(.group 5 41 false)⟩))))
(.branch 49163
(.branch 49149
(.branch 49142
(.leaf ⟨49135,7,(.group 5 42 false)⟩)
(.leaf ⟨49142,7,(.group 5 43 false)⟩))
(.branch 49156
(.leaf ⟨49149,7,(.group 5 44 false)⟩)
(.leaf ⟨49156,7,(.group 5 45 false)⟩)))
(.branch 49177
(.branch 49170
(.leaf ⟨49163,7,(.group 5 46 false)⟩)
(.leaf ⟨49170,7,(.group 5 47 false)⟩))
(.branch 49184
(.leaf ⟨49177,7,(.group 5 48 false)⟩)
(.leaf ⟨49184,7,(.group 5 49 false)⟩)))))))

theorem tree39_checked : tree39.check 48697 49191 = true := by decide +kernel

def tree40 : Tree := (.branch 49415
(.branch 49303
(.branch 49247
(.branch 49219
(.branch 49205
(.branch 49198
(.leaf ⟨49191,7,(.group 5 50 false)⟩)
(.leaf ⟨49198,7,(.group 5 51 false)⟩))
(.branch 49212
(.leaf ⟨49205,7,(.group 5 52 false)⟩)
(.leaf ⟨49212,7,(.group 5 53 false)⟩)))
(.branch 49233
(.branch 49226
(.leaf ⟨49219,7,(.group 5 54 false)⟩)
(.leaf ⟨49226,7,(.group 5 55 false)⟩))
(.branch 49240
(.leaf ⟨49233,7,(.group 5 56 false)⟩)
(.leaf ⟨49240,7,(.group 5 57 false)⟩))))
(.branch 49275
(.branch 49261
(.branch 49254
(.leaf ⟨49247,7,(.group 5 58 false)⟩)
(.leaf ⟨49254,7,(.group 5 59 false)⟩))
(.branch 49268
(.leaf ⟨49261,7,(.group 5 60 false)⟩)
(.leaf ⟨49268,7,(.group 5 61 false)⟩)))
(.branch 49289
(.branch 49282
(.leaf ⟨49275,7,(.group 5 62 false)⟩)
(.leaf ⟨49282,7,(.group 5 63 false)⟩))
(.branch 49296
(.leaf ⟨49289,7,(.group 5 64 false)⟩)
(.leaf ⟨49296,7,(.group 5 65 false)⟩)))))
(.branch 49359
(.branch 49331
(.branch 49317
(.branch 49310
(.leaf ⟨49303,7,(.group 5 66 false)⟩)
(.leaf ⟨49310,7,(.group 5 67 false)⟩))
(.branch 49324
(.leaf ⟨49317,7,(.group 5 68 false)⟩)
(.leaf ⟨49324,7,(.group 5 69 false)⟩)))
(.branch 49345
(.branch 49338
(.leaf ⟨49331,7,(.group 5 70 false)⟩)
(.leaf ⟨49338,7,(.group 5 71 false)⟩))
(.branch 49352
(.leaf ⟨49345,7,(.group 5 72 false)⟩)
(.leaf ⟨49352,7,(.group 5 73 false)⟩))))
(.branch 49387
(.branch 49373
(.branch 49366
(.leaf ⟨49359,7,(.group 5 74 false)⟩)
(.leaf ⟨49366,7,(.group 5 75 false)⟩))
(.branch 49380
(.leaf ⟨49373,7,(.group 5 76 false)⟩)
(.leaf ⟨49380,7,(.group 5 77 false)⟩)))
(.branch 49401
(.branch 49394
(.leaf ⟨49387,7,(.group 5 78 false)⟩)
(.leaf ⟨49394,7,(.group 5 79 false)⟩))
(.branch 49408
(.leaf ⟨49401,7,(.group 5 80 false)⟩)
(.leaf ⟨49408,7,(.group 5 81 false)⟩))))))
(.branch 49527
(.branch 49471
(.branch 49443
(.branch 49429
(.branch 49422
(.leaf ⟨49415,7,(.group 5 82 false)⟩)
(.leaf ⟨49422,7,(.group 5 83 false)⟩))
(.branch 49436
(.leaf ⟨49429,7,(.group 5 84 false)⟩)
(.leaf ⟨49436,7,(.group 5 85 false)⟩)))
(.branch 49457
(.branch 49450
(.leaf ⟨49443,7,(.group 5 86 false)⟩)
(.leaf ⟨49450,7,(.group 5 87 false)⟩))
(.branch 49464
(.leaf ⟨49457,7,(.group 5 88 false)⟩)
(.leaf ⟨49464,7,(.group 5 89 false)⟩))))
(.branch 49499
(.branch 49485
(.branch 49478
(.leaf ⟨49471,7,(.group 5 90 false)⟩)
(.leaf ⟨49478,7,(.group 5 91 false)⟩))
(.branch 49492
(.leaf ⟨49485,7,(.group 5 92 false)⟩)
(.leaf ⟨49492,7,(.group 5 93 false)⟩)))
(.branch 49513
(.branch 49506
(.leaf ⟨49499,7,(.group 5 94 false)⟩)
(.leaf ⟨49506,7,(.group 5 95 false)⟩))
(.branch 49520
(.leaf ⟨49513,7,(.group 5 96 false)⟩)
(.leaf ⟨49520,7,(.group 5 97 false)⟩)))))
(.branch 49583
(.branch 49555
(.branch 49541
(.branch 49534
(.leaf ⟨49527,7,(.group 5 98 false)⟩)
(.leaf ⟨49534,7,(.group 5 99 false)⟩))
(.branch 49548
(.leaf ⟨49541,7,(.group 5 100 false)⟩)
(.leaf ⟨49548,7,(.group 5 101 false)⟩)))
(.branch 49569
(.branch 49562
(.leaf ⟨49555,7,(.group 5 102 false)⟩)
(.leaf ⟨49562,7,(.group 5 103 false)⟩))
(.branch 49576
(.leaf ⟨49569,7,(.group 5 104 false)⟩)
(.leaf ⟨49576,7,(.group 5 105 false)⟩))))
(.branch 49611
(.branch 49597
(.branch 49590
(.leaf ⟨49583,7,(.group 5 106 false)⟩)
(.leaf ⟨49590,7,(.group 5 107 false)⟩))
(.branch 49604
(.leaf ⟨49597,7,(.group 5 108 false)⟩)
(.leaf ⟨49604,7,(.group 5 109 false)⟩)))
(.branch 49625
(.branch 49618
(.leaf ⟨49611,7,(.group 5 110 false)⟩)
(.leaf ⟨49618,7,(.group 5 111 false)⟩))
(.branch 49632
(.leaf ⟨49625,7,(.group 5 112 false)⟩)
(.leaf ⟨49632,7,(.group 5 113 false)⟩)))))))

theorem tree40_checked : tree40.check 49191 49639 = true := by decide +kernel

def tree41 : Tree := (.branch 49863
(.branch 49751
(.branch 49695
(.branch 49667
(.branch 49653
(.branch 49646
(.leaf ⟨49639,7,(.group 5 114 false)⟩)
(.leaf ⟨49646,7,(.group 5 115 false)⟩))
(.branch 49660
(.leaf ⟨49653,7,(.group 5 116 false)⟩)
(.leaf ⟨49660,7,(.group 5 117 false)⟩)))
(.branch 49681
(.branch 49674
(.leaf ⟨49667,7,(.group 5 118 false)⟩)
(.leaf ⟨49674,7,(.group 5 119 false)⟩))
(.branch 49688
(.leaf ⟨49681,7,(.group 5 120 false)⟩)
(.leaf ⟨49688,7,(.group 5 121 false)⟩))))
(.branch 49723
(.branch 49709
(.branch 49702
(.leaf ⟨49695,7,(.group 5 122 false)⟩)
(.leaf ⟨49702,7,(.group 5 123 false)⟩))
(.branch 49716
(.leaf ⟨49709,7,(.group 5 124 false)⟩)
(.leaf ⟨49716,7,(.group 5 125 false)⟩)))
(.branch 49737
(.branch 49730
(.leaf ⟨49723,7,(.group 5 126 false)⟩)
(.leaf ⟨49730,7,(.group 5 127 false)⟩))
(.branch 49744
(.leaf ⟨49737,7,(.group 5 128 false)⟩)
(.leaf ⟨49744,7,(.group 5 129 false)⟩)))))
(.branch 49807
(.branch 49779
(.branch 49765
(.branch 49758
(.leaf ⟨49751,7,(.group 5 130 false)⟩)
(.leaf ⟨49758,7,(.group 5 131 false)⟩))
(.branch 49772
(.leaf ⟨49765,7,(.group 5 132 false)⟩)
(.leaf ⟨49772,7,(.group 5 133 false)⟩)))
(.branch 49793
(.branch 49786
(.leaf ⟨49779,7,(.group 5 134 false)⟩)
(.leaf ⟨49786,7,(.group 5 135 false)⟩))
(.branch 49800
(.leaf ⟨49793,7,(.group 5 136 false)⟩)
(.leaf ⟨49800,7,(.group 5 137 false)⟩))))
(.branch 49835
(.branch 49821
(.branch 49814
(.leaf ⟨49807,7,(.group 5 138 false)⟩)
(.leaf ⟨49814,7,(.group 5 139 false)⟩))
(.branch 49828
(.leaf ⟨49821,7,(.group 5 140 false)⟩)
(.leaf ⟨49828,7,(.group 5 141 false)⟩)))
(.branch 49849
(.branch 49842
(.leaf ⟨49835,7,(.group 5 142 false)⟩)
(.leaf ⟨49842,7,(.group 5 143 false)⟩))
(.branch 49856
(.leaf ⟨49849,7,(.group 5 144 false)⟩)
(.leaf ⟨49856,7,(.group 5 145 false)⟩))))))
(.branch 49975
(.branch 49919
(.branch 49891
(.branch 49877
(.branch 49870
(.leaf ⟨49863,7,(.group 5 146 false)⟩)
(.leaf ⟨49870,7,(.group 5 147 false)⟩))
(.branch 49884
(.leaf ⟨49877,7,(.group 5 148 false)⟩)
(.leaf ⟨49884,7,(.group 5 149 false)⟩)))
(.branch 49905
(.branch 49898
(.leaf ⟨49891,7,(.group 5 150 false)⟩)
(.leaf ⟨49898,7,(.group 5 151 false)⟩))
(.branch 49912
(.leaf ⟨49905,7,(.group 5 152 false)⟩)
(.leaf ⟨49912,7,(.group 5 153 false)⟩))))
(.branch 49947
(.branch 49933
(.branch 49926
(.leaf ⟨49919,7,(.group 5 154 false)⟩)
(.leaf ⟨49926,7,(.group 5 155 false)⟩))
(.branch 49940
(.leaf ⟨49933,7,(.group 5 156 false)⟩)
(.leaf ⟨49940,7,(.group 5 157 false)⟩)))
(.branch 49961
(.branch 49954
(.leaf ⟨49947,7,(.group 5 158 false)⟩)
(.leaf ⟨49954,7,(.group 5 159 false)⟩))
(.branch 49968
(.leaf ⟨49961,7,(.group 5 160 false)⟩)
(.leaf ⟨49968,7,(.group 5 161 false)⟩)))))
(.branch 50031
(.branch 50003
(.branch 49989
(.branch 49982
(.leaf ⟨49975,7,(.group 5 162 false)⟩)
(.leaf ⟨49982,7,(.group 5 163 false)⟩))
(.branch 49996
(.leaf ⟨49989,7,(.group 5 164 false)⟩)
(.leaf ⟨49996,7,(.group 5 165 false)⟩)))
(.branch 50017
(.branch 50010
(.leaf ⟨50003,7,(.group 5 166 false)⟩)
(.leaf ⟨50010,7,(.group 5 167 false)⟩))
(.branch 50024
(.leaf ⟨50017,7,(.group 5 168 false)⟩)
(.leaf ⟨50024,7,(.group 5 169 false)⟩))))
(.branch 50059
(.branch 50045
(.branch 50038
(.leaf ⟨50031,7,(.group 5 170 false)⟩)
(.leaf ⟨50038,7,(.group 5 171 false)⟩))
(.branch 50052
(.leaf ⟨50045,7,(.group 5 172 false)⟩)
(.leaf ⟨50052,7,(.group 5 173 false)⟩)))
(.branch 50073
(.branch 50066
(.leaf ⟨50059,7,(.group 5 174 false)⟩)
(.leaf ⟨50066,7,(.group 5 175 false)⟩))
(.branch 50080
(.leaf ⟨50073,7,(.group 5 176 false)⟩)
(.leaf ⟨50080,7,(.group 5 177 false)⟩)))))))

theorem tree41_checked : tree41.check 49639 50087 = true := by decide +kernel

def tree42 : Tree := (.branch 50311
(.branch 50199
(.branch 50143
(.branch 50115
(.branch 50101
(.branch 50094
(.leaf ⟨50087,7,(.group 5 178 false)⟩)
(.leaf ⟨50094,7,(.group 5 179 false)⟩))
(.branch 50108
(.leaf ⟨50101,7,(.group 5 180 false)⟩)
(.leaf ⟨50108,7,(.group 5 181 false)⟩)))
(.branch 50129
(.branch 50122
(.leaf ⟨50115,7,(.group 5 182 false)⟩)
(.leaf ⟨50122,7,(.group 5 183 false)⟩))
(.branch 50136
(.leaf ⟨50129,7,(.group 5 184 false)⟩)
(.leaf ⟨50136,7,(.group 5 185 false)⟩))))
(.branch 50171
(.branch 50157
(.branch 50150
(.leaf ⟨50143,7,(.group 5 186 false)⟩)
(.leaf ⟨50150,7,(.group 5 187 false)⟩))
(.branch 50164
(.leaf ⟨50157,7,(.group 5 188 false)⟩)
(.leaf ⟨50164,7,(.group 5 189 false)⟩)))
(.branch 50185
(.branch 50178
(.leaf ⟨50171,7,(.group 5 190 false)⟩)
(.leaf ⟨50178,7,(.group 5 191 false)⟩))
(.branch 50192
(.leaf ⟨50185,7,(.group 5 192 false)⟩)
(.leaf ⟨50192,7,(.group 5 193 false)⟩)))))
(.branch 50255
(.branch 50227
(.branch 50213
(.branch 50206
(.leaf ⟨50199,7,(.group 5 194 false)⟩)
(.leaf ⟨50206,7,(.group 5 195 false)⟩))
(.branch 50220
(.leaf ⟨50213,7,(.group 5 196 false)⟩)
(.leaf ⟨50220,7,(.group 5 197 false)⟩)))
(.branch 50241
(.branch 50234
(.leaf ⟨50227,7,(.group 5 198 false)⟩)
(.leaf ⟨50234,7,(.group 5 199 false)⟩))
(.branch 50248
(.leaf ⟨50241,7,(.group 5 200 false)⟩)
(.leaf ⟨50248,7,(.group 5 201 false)⟩))))
(.branch 50283
(.branch 50269
(.branch 50262
(.leaf ⟨50255,7,(.group 5 202 false)⟩)
(.leaf ⟨50262,7,(.group 5 203 false)⟩))
(.branch 50276
(.leaf ⟨50269,7,(.group 5 204 false)⟩)
(.leaf ⟨50276,7,(.group 5 205 false)⟩)))
(.branch 50297
(.branch 50290
(.leaf ⟨50283,7,(.group 5 206 false)⟩)
(.leaf ⟨50290,7,(.group 5 207 false)⟩))
(.branch 50304
(.leaf ⟨50297,7,(.group 5 208 false)⟩)
(.leaf ⟨50304,7,(.group 5 209 false)⟩))))))
(.branch 50423
(.branch 50367
(.branch 50339
(.branch 50325
(.branch 50318
(.leaf ⟨50311,7,(.group 5 210 false)⟩)
(.leaf ⟨50318,7,(.group 5 211 false)⟩))
(.branch 50332
(.leaf ⟨50325,7,(.group 5 212 false)⟩)
(.leaf ⟨50332,7,(.group 5 213 false)⟩)))
(.branch 50353
(.branch 50346
(.leaf ⟨50339,7,(.group 5 214 false)⟩)
(.leaf ⟨50346,7,(.group 5 215 false)⟩))
(.branch 50360
(.leaf ⟨50353,7,(.group 5 216 false)⟩)
(.leaf ⟨50360,7,(.group 5 217 false)⟩))))
(.branch 50395
(.branch 50381
(.branch 50374
(.leaf ⟨50367,7,(.group 5 218 false)⟩)
(.leaf ⟨50374,7,(.group 5 219 false)⟩))
(.branch 50388
(.leaf ⟨50381,7,(.group 5 220 false)⟩)
(.leaf ⟨50388,7,(.group 5 221 false)⟩)))
(.branch 50409
(.branch 50402
(.leaf ⟨50395,7,(.group 5 222 false)⟩)
(.leaf ⟨50402,7,(.group 5 223 false)⟩))
(.branch 50416
(.leaf ⟨50409,7,(.group 5 224 false)⟩)
(.leaf ⟨50416,7,(.group 5 225 false)⟩)))))
(.branch 50479
(.branch 50451
(.branch 50437
(.branch 50430
(.leaf ⟨50423,7,(.group 5 226 false)⟩)
(.leaf ⟨50430,7,(.group 5 227 false)⟩))
(.branch 50444
(.leaf ⟨50437,7,(.group 5 228 false)⟩)
(.leaf ⟨50444,7,(.group 5 229 false)⟩)))
(.branch 50465
(.branch 50458
(.leaf ⟨50451,7,(.group 5 230 false)⟩)
(.leaf ⟨50458,7,(.group 5 231 false)⟩))
(.branch 50472
(.leaf ⟨50465,7,(.group 5 232 false)⟩)
(.leaf ⟨50472,7,(.group 5 233 false)⟩))))
(.branch 50507
(.branch 50493
(.branch 50486
(.leaf ⟨50479,7,(.group 5 234 false)⟩)
(.leaf ⟨50486,7,(.group 5 235 false)⟩))
(.branch 50500
(.leaf ⟨50493,7,(.group 5 236 false)⟩)
(.leaf ⟨50500,7,(.group 5 237 false)⟩)))
(.branch 50521
(.branch 50514
(.leaf ⟨50507,7,(.group 5 238 false)⟩)
(.leaf ⟨50514,7,(.group 5 239 false)⟩))
(.branch 50528
(.leaf ⟨50521,7,(.group 5 240 false)⟩)
(.leaf ⟨50528,7,(.group 5 241 false)⟩)))))))

theorem tree42_checked : tree42.check 50087 50535 = true := by decide +kernel

def tree43 : Tree := (.branch 50759
(.branch 50647
(.branch 50591
(.branch 50563
(.branch 50549
(.branch 50542
(.leaf ⟨50535,7,(.group 5 242 false)⟩)
(.leaf ⟨50542,7,(.group 5 243 false)⟩))
(.branch 50556
(.leaf ⟨50549,7,(.group 5 244 false)⟩)
(.leaf ⟨50556,7,(.group 5 245 false)⟩)))
(.branch 50577
(.branch 50570
(.leaf ⟨50563,7,(.group 5 246 false)⟩)
(.leaf ⟨50570,7,(.group 5 247 false)⟩))
(.branch 50584
(.leaf ⟨50577,7,(.group 5 248 false)⟩)
(.leaf ⟨50584,7,(.group 5 249 false)⟩))))
(.branch 50619
(.branch 50605
(.branch 50598
(.leaf ⟨50591,7,(.group 5 250 false)⟩)
(.leaf ⟨50598,7,(.group 5 251 false)⟩))
(.branch 50612
(.leaf ⟨50605,7,(.group 5 252 false)⟩)
(.leaf ⟨50612,7,(.group 5 253 false)⟩)))
(.branch 50633
(.branch 50626
(.leaf ⟨50619,7,(.group 5 254 false)⟩)
(.leaf ⟨50626,7,(.group 5 255 false)⟩))
(.branch 50640
(.leaf ⟨50633,7,(.group 5 256 false)⟩)
(.leaf ⟨50640,7,(.group 5 257 false)⟩)))))
(.branch 50703
(.branch 50675
(.branch 50661
(.branch 50654
(.leaf ⟨50647,7,(.group 5 258 false)⟩)
(.leaf ⟨50654,7,(.group 5 259 false)⟩))
(.branch 50668
(.leaf ⟨50661,7,(.group 5 260 false)⟩)
(.leaf ⟨50668,7,(.group 5 261 false)⟩)))
(.branch 50689
(.branch 50682
(.leaf ⟨50675,7,(.group 5 262 false)⟩)
(.leaf ⟨50682,7,(.group 5 263 false)⟩))
(.branch 50696
(.leaf ⟨50689,7,(.group 5 264 false)⟩)
(.leaf ⟨50696,7,(.group 5 265 false)⟩))))
(.branch 50731
(.branch 50717
(.branch 50710
(.leaf ⟨50703,7,(.group 5 266 false)⟩)
(.leaf ⟨50710,7,(.group 5 267 false)⟩))
(.branch 50724
(.leaf ⟨50717,7,(.group 5 268 false)⟩)
(.leaf ⟨50724,7,(.group 5 269 false)⟩)))
(.branch 50745
(.branch 50738
(.leaf ⟨50731,7,(.group 5 270 false)⟩)
(.leaf ⟨50738,7,(.group 5 271 false)⟩))
(.branch 50752
(.leaf ⟨50745,7,(.group 5 272 false)⟩)
(.leaf ⟨50752,7,(.group 5 273 false)⟩))))))
(.branch 50871
(.branch 50815
(.branch 50787
(.branch 50773
(.branch 50766
(.leaf ⟨50759,7,(.group 5 274 false)⟩)
(.leaf ⟨50766,7,(.group 5 275 false)⟩))
(.branch 50780
(.leaf ⟨50773,7,(.group 5 276 false)⟩)
(.leaf ⟨50780,7,(.group 5 277 false)⟩)))
(.branch 50801
(.branch 50794
(.leaf ⟨50787,7,(.group 5 278 false)⟩)
(.leaf ⟨50794,7,(.group 5 279 false)⟩))
(.branch 50808
(.leaf ⟨50801,7,(.group 5 280 false)⟩)
(.leaf ⟨50808,7,(.group 5 281 false)⟩))))
(.branch 50843
(.branch 50829
(.branch 50822
(.leaf ⟨50815,7,(.group 5 282 false)⟩)
(.leaf ⟨50822,7,(.group 5 283 false)⟩))
(.branch 50836
(.leaf ⟨50829,7,(.group 5 284 false)⟩)
(.leaf ⟨50836,7,(.group 5 285 false)⟩)))
(.branch 50857
(.branch 50850
(.leaf ⟨50843,7,(.group 5 286 false)⟩)
(.leaf ⟨50850,7,(.group 5 287 false)⟩))
(.branch 50864
(.leaf ⟨50857,7,(.group 5 288 false)⟩)
(.leaf ⟨50864,7,(.group 5 289 false)⟩)))))
(.branch 50927
(.branch 50899
(.branch 50885
(.branch 50878
(.leaf ⟨50871,7,(.group 5 290 false)⟩)
(.leaf ⟨50878,7,(.group 5 291 false)⟩))
(.branch 50892
(.leaf ⟨50885,7,(.group 5 292 false)⟩)
(.leaf ⟨50892,7,(.group 5 293 false)⟩)))
(.branch 50913
(.branch 50906
(.leaf ⟨50899,7,(.group 5 294 false)⟩)
(.leaf ⟨50906,7,(.group 5 295 false)⟩))
(.branch 50920
(.leaf ⟨50913,7,(.group 5 296 false)⟩)
(.leaf ⟨50920,7,(.group 5 297 false)⟩))))
(.branch 50955
(.branch 50941
(.branch 50934
(.leaf ⟨50927,7,(.group 5 298 false)⟩)
(.leaf ⟨50934,7,(.group 5 299 false)⟩))
(.branch 50948
(.leaf ⟨50941,7,(.group 5 300 false)⟩)
(.leaf ⟨50948,7,(.group 5 301 false)⟩)))
(.branch 50969
(.branch 50962
(.leaf ⟨50955,7,(.group 5 302 false)⟩)
(.leaf ⟨50962,7,(.group 5 303 false)⟩))
(.branch 50976
(.leaf ⟨50969,7,(.group 5 304 false)⟩)
(.leaf ⟨50976,7,(.group 5 305 false)⟩)))))))

theorem tree43_checked : tree43.check 50535 50983 = true := by decide +kernel

def tree44 : Tree := (.branch 51207
(.branch 51095
(.branch 51039
(.branch 51011
(.branch 50997
(.branch 50990
(.leaf ⟨50983,7,(.group 5 306 false)⟩)
(.leaf ⟨50990,7,(.group 5 307 false)⟩))
(.branch 51004
(.leaf ⟨50997,7,(.group 5 308 false)⟩)
(.leaf ⟨51004,7,(.group 5 309 false)⟩)))
(.branch 51025
(.branch 51018
(.leaf ⟨51011,7,(.group 5 310 false)⟩)
(.leaf ⟨51018,7,(.group 5 311 false)⟩))
(.branch 51032
(.leaf ⟨51025,7,(.group 5 312 false)⟩)
(.leaf ⟨51032,7,(.group 5 313 false)⟩))))
(.branch 51067
(.branch 51053
(.branch 51046
(.leaf ⟨51039,7,(.group 5 314 false)⟩)
(.leaf ⟨51046,7,(.group 5 315 false)⟩))
(.branch 51060
(.leaf ⟨51053,7,(.group 5 316 false)⟩)
(.leaf ⟨51060,7,(.group 5 317 false)⟩)))
(.branch 51081
(.branch 51074
(.leaf ⟨51067,7,(.group 5 318 false)⟩)
(.leaf ⟨51074,7,(.group 5 319 false)⟩))
(.branch 51088
(.leaf ⟨51081,7,(.group 5 320 false)⟩)
(.leaf ⟨51088,7,(.group 5 321 false)⟩)))))
(.branch 51151
(.branch 51123
(.branch 51109
(.branch 51102
(.leaf ⟨51095,7,(.group 5 322 false)⟩)
(.leaf ⟨51102,7,(.group 5 323 false)⟩))
(.branch 51116
(.leaf ⟨51109,7,(.group 5 324 false)⟩)
(.leaf ⟨51116,7,(.group 5 325 false)⟩)))
(.branch 51137
(.branch 51130
(.leaf ⟨51123,7,(.group 5 326 false)⟩)
(.leaf ⟨51130,7,(.group 5 327 false)⟩))
(.branch 51144
(.leaf ⟨51137,7,(.group 5 328 false)⟩)
(.leaf ⟨51144,7,(.group 5 329 false)⟩))))
(.branch 51179
(.branch 51165
(.branch 51158
(.leaf ⟨51151,7,(.group 5 330 false)⟩)
(.leaf ⟨51158,7,(.group 5 331 false)⟩))
(.branch 51172
(.leaf ⟨51165,7,(.group 5 332 false)⟩)
(.leaf ⟨51172,7,(.group 5 333 false)⟩)))
(.branch 51193
(.branch 51186
(.leaf ⟨51179,7,(.group 5 334 false)⟩)
(.leaf ⟨51186,7,(.group 5 335 false)⟩))
(.branch 51200
(.leaf ⟨51193,7,(.group 5 336 false)⟩)
(.leaf ⟨51200,7,(.group 5 337 false)⟩))))))
(.branch 51319
(.branch 51263
(.branch 51235
(.branch 51221
(.branch 51214
(.leaf ⟨51207,7,(.group 5 338 false)⟩)
(.leaf ⟨51214,7,(.group 5 339 false)⟩))
(.branch 51228
(.leaf ⟨51221,7,(.group 5 340 false)⟩)
(.leaf ⟨51228,7,(.group 5 341 false)⟩)))
(.branch 51249
(.branch 51242
(.leaf ⟨51235,7,(.group 5 342 false)⟩)
(.leaf ⟨51242,7,(.group 5 343 false)⟩))
(.branch 51256
(.leaf ⟨51249,7,(.group 5 344 false)⟩)
(.leaf ⟨51256,7,(.group 5 345 false)⟩))))
(.branch 51291
(.branch 51277
(.branch 51270
(.leaf ⟨51263,7,(.group 5 346 false)⟩)
(.leaf ⟨51270,7,(.group 5 347 false)⟩))
(.branch 51284
(.leaf ⟨51277,7,(.group 5 348 false)⟩)
(.leaf ⟨51284,7,(.group 5 349 false)⟩)))
(.branch 51305
(.branch 51298
(.leaf ⟨51291,7,(.group 5 350 false)⟩)
(.leaf ⟨51298,7,(.group 5 351 false)⟩))
(.branch 51312
(.leaf ⟨51305,7,(.group 5 352 false)⟩)
(.leaf ⟨51312,7,(.group 5 353 false)⟩)))))
(.branch 51375
(.branch 51347
(.branch 51333
(.branch 51326
(.leaf ⟨51319,7,(.group 5 354 false)⟩)
(.leaf ⟨51326,7,(.group 5 355 false)⟩))
(.branch 51340
(.leaf ⟨51333,7,(.group 5 356 false)⟩)
(.leaf ⟨51340,7,(.group 5 357 false)⟩)))
(.branch 51361
(.branch 51354
(.leaf ⟨51347,7,(.group 5 358 false)⟩)
(.leaf ⟨51354,7,(.group 5 359 false)⟩))
(.branch 51368
(.leaf ⟨51361,7,(.group 5 360 false)⟩)
(.leaf ⟨51368,7,(.group 5 361 false)⟩))))
(.branch 51403
(.branch 51389
(.branch 51382
(.leaf ⟨51375,7,(.group 5 362 false)⟩)
(.leaf ⟨51382,7,(.group 5 363 false)⟩))
(.branch 51396
(.leaf ⟨51389,7,(.group 5 364 false)⟩)
(.leaf ⟨51396,7,(.group 5 365 false)⟩)))
(.branch 51417
(.branch 51410
(.leaf ⟨51403,7,(.group 5 366 false)⟩)
(.leaf ⟨51410,7,(.group 5 367 false)⟩))
(.branch 51424
(.leaf ⟨51417,7,(.group 5 368 false)⟩)
(.leaf ⟨51424,7,(.group 5 369 false)⟩)))))))

theorem tree44_checked : tree44.check 50983 51431 = true := by decide +kernel

def tree45 : Tree := (.branch 51655
(.branch 51543
(.branch 51487
(.branch 51459
(.branch 51445
(.branch 51438
(.leaf ⟨51431,7,(.group 5 370 false)⟩)
(.leaf ⟨51438,7,(.group 5 371 false)⟩))
(.branch 51452
(.leaf ⟨51445,7,(.group 5 372 false)⟩)
(.leaf ⟨51452,7,(.group 5 373 false)⟩)))
(.branch 51473
(.branch 51466
(.leaf ⟨51459,7,(.group 5 374 false)⟩)
(.leaf ⟨51466,7,(.group 5 375 false)⟩))
(.branch 51480
(.leaf ⟨51473,7,(.group 5 376 false)⟩)
(.leaf ⟨51480,7,(.group 5 377 false)⟩))))
(.branch 51515
(.branch 51501
(.branch 51494
(.leaf ⟨51487,7,(.group 5 378 false)⟩)
(.leaf ⟨51494,7,(.group 5 379 false)⟩))
(.branch 51508
(.leaf ⟨51501,7,(.group 5 380 false)⟩)
(.leaf ⟨51508,7,(.group 5 381 false)⟩)))
(.branch 51529
(.branch 51522
(.leaf ⟨51515,7,(.group 5 382 false)⟩)
(.leaf ⟨51522,7,(.group 5 383 false)⟩))
(.branch 51536
(.leaf ⟨51529,7,(.group 5 384 false)⟩)
(.leaf ⟨51536,7,(.group 5 385 false)⟩)))))
(.branch 51599
(.branch 51571
(.branch 51557
(.branch 51550
(.leaf ⟨51543,7,(.group 5 386 false)⟩)
(.leaf ⟨51550,7,(.group 5 387 false)⟩))
(.branch 51564
(.leaf ⟨51557,7,(.group 5 388 false)⟩)
(.leaf ⟨51564,7,(.group 5 389 false)⟩)))
(.branch 51585
(.branch 51578
(.leaf ⟨51571,7,(.group 5 390 false)⟩)
(.leaf ⟨51578,7,(.group 5 391 false)⟩))
(.branch 51592
(.leaf ⟨51585,7,(.group 5 392 false)⟩)
(.leaf ⟨51592,7,(.group 5 393 false)⟩))))
(.branch 51627
(.branch 51613
(.branch 51606
(.leaf ⟨51599,7,(.group 5 394 false)⟩)
(.leaf ⟨51606,7,(.group 5 395 false)⟩))
(.branch 51620
(.leaf ⟨51613,7,(.group 5 396 false)⟩)
(.leaf ⟨51620,7,(.group 5 397 false)⟩)))
(.branch 51641
(.branch 51634
(.leaf ⟨51627,7,(.group 5 398 false)⟩)
(.leaf ⟨51634,7,(.group 5 399 false)⟩))
(.branch 51648
(.leaf ⟨51641,7,(.group 5 400 false)⟩)
(.leaf ⟨51648,7,(.group 5 401 false)⟩))))))
(.branch 51767
(.branch 51711
(.branch 51683
(.branch 51669
(.branch 51662
(.leaf ⟨51655,7,(.group 5 402 false)⟩)
(.leaf ⟨51662,7,(.group 5 403 false)⟩))
(.branch 51676
(.leaf ⟨51669,7,(.group 5 404 false)⟩)
(.leaf ⟨51676,7,(.group 5 405 false)⟩)))
(.branch 51697
(.branch 51690
(.leaf ⟨51683,7,(.group 5 406 false)⟩)
(.leaf ⟨51690,7,(.group 5 407 false)⟩))
(.branch 51704
(.leaf ⟨51697,7,(.group 5 408 false)⟩)
(.leaf ⟨51704,7,(.group 5 409 false)⟩))))
(.branch 51739
(.branch 51725
(.branch 51718
(.leaf ⟨51711,7,(.group 5 410 false)⟩)
(.leaf ⟨51718,7,(.group 5 411 false)⟩))
(.branch 51732
(.leaf ⟨51725,7,(.group 5 412 false)⟩)
(.leaf ⟨51732,7,(.group 5 413 false)⟩)))
(.branch 51753
(.branch 51746
(.leaf ⟨51739,7,(.group 5 414 false)⟩)
(.leaf ⟨51746,7,(.group 5 415 false)⟩))
(.branch 51760
(.leaf ⟨51753,7,(.group 5 416 false)⟩)
(.leaf ⟨51760,7,(.group 5 417 false)⟩)))))
(.branch 51823
(.branch 51795
(.branch 51781
(.branch 51774
(.leaf ⟨51767,7,(.group 5 418 false)⟩)
(.leaf ⟨51774,7,(.group 5 419 false)⟩))
(.branch 51788
(.leaf ⟨51781,7,(.group 5 420 false)⟩)
(.leaf ⟨51788,7,(.group 5 421 false)⟩)))
(.branch 51809
(.branch 51802
(.leaf ⟨51795,7,(.group 5 422 false)⟩)
(.leaf ⟨51802,7,(.group 5 423 false)⟩))
(.branch 51816
(.leaf ⟨51809,7,(.group 5 424 false)⟩)
(.leaf ⟨51816,7,(.group 5 425 false)⟩))))
(.branch 51851
(.branch 51837
(.branch 51830
(.leaf ⟨51823,7,(.group 5 426 false)⟩)
(.leaf ⟨51830,7,(.group 5 427 false)⟩))
(.branch 51844
(.leaf ⟨51837,7,(.group 5 428 false)⟩)
(.leaf ⟨51844,7,(.group 5 429 false)⟩)))
(.branch 51865
(.branch 51858
(.leaf ⟨51851,7,(.group 5 430 false)⟩)
(.leaf ⟨51858,7,(.group 5 431 false)⟩))
(.branch 51872
(.leaf ⟨51865,7,(.group 5 432 false)⟩)
(.leaf ⟨51872,7,(.group 5 433 false)⟩)))))))

theorem tree45_checked : tree45.check 51431 51879 = true := by decide +kernel

def tree46 : Tree := (.branch 52103
(.branch 51991
(.branch 51935
(.branch 51907
(.branch 51893
(.branch 51886
(.leaf ⟨51879,7,(.group 5 434 false)⟩)
(.leaf ⟨51886,7,(.group 5 435 false)⟩))
(.branch 51900
(.leaf ⟨51893,7,(.group 5 436 false)⟩)
(.leaf ⟨51900,7,(.group 5 437 false)⟩)))
(.branch 51921
(.branch 51914
(.leaf ⟨51907,7,(.group 5 438 false)⟩)
(.leaf ⟨51914,7,(.group 5 439 false)⟩))
(.branch 51928
(.leaf ⟨51921,7,(.group 5 440 false)⟩)
(.leaf ⟨51928,7,(.group 5 441 false)⟩))))
(.branch 51963
(.branch 51949
(.branch 51942
(.leaf ⟨51935,7,(.group 5 442 false)⟩)
(.leaf ⟨51942,7,(.group 5 443 false)⟩))
(.branch 51956
(.leaf ⟨51949,7,(.group 5 444 false)⟩)
(.leaf ⟨51956,7,(.group 5 445 false)⟩)))
(.branch 51977
(.branch 51970
(.leaf ⟨51963,7,(.group 5 446 false)⟩)
(.leaf ⟨51970,7,(.group 5 447 false)⟩))
(.branch 51984
(.leaf ⟨51977,7,(.group 5 448 false)⟩)
(.leaf ⟨51984,7,(.group 5 449 false)⟩)))))
(.branch 52047
(.branch 52019
(.branch 52005
(.branch 51998
(.leaf ⟨51991,7,(.group 5 450 false)⟩)
(.leaf ⟨51998,7,(.group 5 451 false)⟩))
(.branch 52012
(.leaf ⟨52005,7,(.group 5 452 false)⟩)
(.leaf ⟨52012,7,(.group 5 453 false)⟩)))
(.branch 52033
(.branch 52026
(.leaf ⟨52019,7,(.group 5 454 false)⟩)
(.leaf ⟨52026,7,(.group 5 455 false)⟩))
(.branch 52040
(.leaf ⟨52033,7,(.group 5 456 false)⟩)
(.leaf ⟨52040,7,(.group 5 457 false)⟩))))
(.branch 52075
(.branch 52061
(.branch 52054
(.leaf ⟨52047,7,(.group 5 458 false)⟩)
(.leaf ⟨52054,7,(.group 5 459 false)⟩))
(.branch 52068
(.leaf ⟨52061,7,(.group 5 460 false)⟩)
(.leaf ⟨52068,7,(.group 5 461 false)⟩)))
(.branch 52089
(.branch 52082
(.leaf ⟨52075,7,(.group 5 462 false)⟩)
(.leaf ⟨52082,7,(.group 5 463 false)⟩))
(.branch 52096
(.leaf ⟨52089,7,(.group 5 464 false)⟩)
(.leaf ⟨52096,7,(.group 5 465 false)⟩))))))
(.branch 52215
(.branch 52159
(.branch 52131
(.branch 52117
(.branch 52110
(.leaf ⟨52103,7,(.group 5 466 false)⟩)
(.leaf ⟨52110,7,(.group 5 467 false)⟩))
(.branch 52124
(.leaf ⟨52117,7,(.group 5 468 false)⟩)
(.leaf ⟨52124,7,(.group 5 469 false)⟩)))
(.branch 52145
(.branch 52138
(.leaf ⟨52131,7,(.group 5 470 false)⟩)
(.leaf ⟨52138,7,(.group 5 471 false)⟩))
(.branch 52152
(.leaf ⟨52145,7,(.group 5 472 false)⟩)
(.leaf ⟨52152,7,(.group 5 473 false)⟩))))
(.branch 52187
(.branch 52173
(.branch 52166
(.leaf ⟨52159,7,(.group 5 474 false)⟩)
(.leaf ⟨52166,7,(.group 5 475 false)⟩))
(.branch 52180
(.leaf ⟨52173,7,(.group 5 476 false)⟩)
(.leaf ⟨52180,7,(.group 5 477 false)⟩)))
(.branch 52201
(.branch 52194
(.leaf ⟨52187,7,(.group 5 478 false)⟩)
(.leaf ⟨52194,7,(.group 5 479 false)⟩))
(.branch 52208
(.leaf ⟨52201,7,(.group 5 480 false)⟩)
(.leaf ⟨52208,7,(.group 5 481 false)⟩)))))
(.branch 52271
(.branch 52243
(.branch 52229
(.branch 52222
(.leaf ⟨52215,7,(.group 5 482 false)⟩)
(.leaf ⟨52222,7,(.group 5 483 false)⟩))
(.branch 52236
(.leaf ⟨52229,7,(.group 5 484 false)⟩)
(.leaf ⟨52236,7,(.group 5 485 false)⟩)))
(.branch 52257
(.branch 52250
(.leaf ⟨52243,7,(.group 5 486 false)⟩)
(.leaf ⟨52250,7,(.group 5 487 false)⟩))
(.branch 52264
(.leaf ⟨52257,7,(.group 5 488 false)⟩)
(.leaf ⟨52264,7,(.group 5 489 false)⟩))))
(.branch 52299
(.branch 52285
(.branch 52278
(.leaf ⟨52271,7,(.group 5 490 false)⟩)
(.leaf ⟨52278,7,(.group 5 491 false)⟩))
(.branch 52292
(.leaf ⟨52285,7,(.group 5 492 false)⟩)
(.leaf ⟨52292,7,(.group 5 493 false)⟩)))
(.branch 52313
(.branch 52306
(.leaf ⟨52299,7,(.group 5 494 false)⟩)
(.leaf ⟨52306,7,(.group 5 495 false)⟩))
(.branch 52320
(.leaf ⟨52313,7,(.group 5 496 false)⟩)
(.leaf ⟨52320,7,(.group 5 497 false)⟩)))))))

theorem tree46_checked : tree46.check 51879 52327 = true := by decide +kernel

def tree47 : Tree := (.branch 52573
(.branch 52445
(.branch 52383
(.branch 52355
(.branch 52341
(.branch 52334
(.leaf ⟨52327,7,(.group 5 498 false)⟩)
(.leaf ⟨52334,7,(.group 6 0 false)⟩))
(.branch 52348
(.leaf ⟨52341,7,(.group 6 1 false)⟩)
(.leaf ⟨52348,7,(.group 6 2 false)⟩)))
(.branch 52369
(.branch 52362
(.leaf ⟨52355,7,(.group 6 3 false)⟩)
(.leaf ⟨52362,7,(.group 6 4 false)⟩))
(.branch 52376
(.leaf ⟨52369,7,(.group 6 5 false)⟩)
(.leaf ⟨52376,7,(.group 6 6 false)⟩))))
(.branch 52413
(.branch 52397
(.branch 52390
(.leaf ⟨52383,7,(.group 6 7 false)⟩)
(.leaf ⟨52390,7,(.group 6 8 false)⟩))
(.branch 52405
(.leaf ⟨52397,8,(.group 0 6 false)⟩)
(.leaf ⟨52405,8,(.group 0 7 false)⟩)))
(.branch 52429
(.branch 52421
(.leaf ⟨52413,8,(.group 0 8 false)⟩)
(.leaf ⟨52421,8,(.group 0 9 false)⟩))
(.branch 52437
(.leaf ⟨52429,8,(.group 0 10 false)⟩)
(.leaf ⟨52437,8,(.group 0 11 false)⟩)))))
(.branch 52509
(.branch 52477
(.branch 52461
(.branch 52453
(.leaf ⟨52445,8,(.group 0 12 false)⟩)
(.leaf ⟨52453,8,(.group 0 13 false)⟩))
(.branch 52469
(.leaf ⟨52461,8,(.group 0 14 false)⟩)
(.leaf ⟨52469,8,(.group 0 15 false)⟩)))
(.branch 52493
(.branch 52485
(.leaf ⟨52477,8,(.group 0 16 false)⟩)
(.leaf ⟨52485,8,(.group 0 17 false)⟩))
(.branch 52501
(.leaf ⟨52493,8,(.group 1 1 false)⟩)
(.leaf ⟨52501,8,(.group 1 2 false)⟩))))
(.branch 52541
(.branch 52525
(.branch 52517
(.leaf ⟨52509,8,(.group 1 3 false)⟩)
(.leaf ⟨52517,8,(.group 2 1 false)⟩))
(.branch 52533
(.leaf ⟨52525,8,(.group 2 2 false)⟩)
(.leaf ⟨52533,8,(.group 2 3 false)⟩)))
(.branch 52557
(.branch 52549
(.leaf ⟨52541,8,(.group 3 1 false)⟩)
(.leaf ⟨52549,8,(.group 3 2 false)⟩))
(.branch 52565
(.leaf ⟨52557,8,(.group 3 3 false)⟩)
(.leaf ⟨52565,8,(.group 4 1 false)⟩))))))
(.branch 52701
(.branch 52637
(.branch 52605
(.branch 52589
(.branch 52581
(.leaf ⟨52573,8,(.group 4 2 false)⟩)
(.leaf ⟨52581,8,(.group 4 3 false)⟩))
(.branch 52597
(.leaf ⟨52589,8,(.group 5 499 false)⟩)
(.leaf ⟨52597,8,(.group 5 500 false)⟩)))
(.branch 52621
(.branch 52613
(.leaf ⟨52605,8,(.group 5 501 false)⟩)
(.leaf ⟨52613,8,(.group 5 502 false)⟩))
(.branch 52629
(.leaf ⟨52621,8,(.group 5 503 false)⟩)
(.leaf ⟨52629,8,(.group 5 504 false)⟩))))
(.branch 52669
(.branch 52653
(.branch 52645
(.leaf ⟨52637,8,(.group 5 505 false)⟩)
(.leaf ⟨52645,8,(.group 5 506 false)⟩))
(.branch 52661
(.leaf ⟨52653,8,(.group 5 507 false)⟩)
(.leaf ⟨52661,8,(.group 5 508 false)⟩)))
(.branch 52685
(.branch 52677
(.leaf ⟨52669,8,(.group 6 10 false)⟩)
(.leaf ⟨52677,8,(.group 6 11 false)⟩))
(.branch 52693
(.leaf ⟨52685,8,(.group 6 12 false)⟩)
(.leaf ⟨52693,8,(.group 6 13 false)⟩)))))
(.branch 52765
(.branch 52733
(.branch 52717
(.branch 52709
(.leaf ⟨52701,8,(.group 6 14 false)⟩)
(.leaf ⟨52709,8,(.group 6 15 false)⟩))
(.branch 52725
(.leaf ⟨52717,8,(.group 6 16 false)⟩)
(.leaf ⟨52725,8,(.group 7 1 false)⟩)))
(.branch 52749
(.branch 52741
(.leaf ⟨52733,8,(.group 7 2 false)⟩)
(.leaf ⟨52741,8,(.group 7 3 false)⟩))
(.branch 52757
(.leaf ⟨52749,8,(.group 7 4 false)⟩)
(.leaf ⟨52757,8,(.group 7 5 false)⟩))))
(.branch 52797
(.branch 52781
(.branch 52773
(.leaf ⟨52765,8,(.group 7 6 false)⟩)
(.leaf ⟨52773,8,(.group 8 9 false)⟩))
(.branch 52789
(.leaf ⟨52781,8,(.group 8 10 false)⟩)
(.leaf ⟨52789,8,(.group 8 11 false)⟩)))
(.branch 52813
(.branch 52805
(.leaf ⟨52797,8,(.group 8 12 false)⟩)
(.leaf ⟨52805,8,(.group 8 13 false)⟩))
(.branch 52821
(.leaf ⟨52813,8,(.group 8 14 false)⟩)
(.leaf ⟨52821,8,(.group 8 15 false)⟩)))))))

theorem tree47_checked : tree47.check 52327 52829 = true := by decide +kernel

def tree48 : Tree := (.branch 53086
(.branch 52957
(.branch 52893
(.branch 52861
(.branch 52845
(.branch 52837
(.leaf ⟨52829,8,(.group 8 16 false)⟩)
(.leaf ⟨52837,8,(.group 8 17 false)⟩))
(.branch 52853
(.leaf ⟨52845,8,(.group 9 12 false)⟩)
(.leaf ⟨52853,8,(.group 9 13 false)⟩)))
(.branch 52877
(.branch 52869
(.leaf ⟨52861,8,(.group 9 14 false)⟩)
(.leaf ⟨52869,8,(.group 9 15 false)⟩))
(.branch 52885
(.leaf ⟨52877,8,(.group 9 16 false)⟩)
(.leaf ⟨52885,8,(.group 9 17 false)⟩))))
(.branch 52925
(.branch 52909
(.branch 52901
(.leaf ⟨52893,8,(.group 10 0 false)⟩)
(.leaf ⟨52901,8,(.group 10 1 false)⟩))
(.branch 52917
(.leaf ⟨52909,8,(.group 10 2 false)⟩)
(.leaf ⟨52917,8,(.group 10 3 false)⟩)))
(.branch 52941
(.branch 52933
(.leaf ⟨52925,8,(.group 10 4 false)⟩)
(.leaf ⟨52933,8,(.group 10 5 false)⟩))
(.branch 52949
(.leaf ⟨52941,8,(.group 10 6 false)⟩)
(.leaf ⟨52949,8,(.group 10 7 false)⟩)))))
(.branch 53021
(.branch 52989
(.branch 52973
(.branch 52965
(.leaf ⟨52957,8,(.group 10 8 false)⟩)
(.leaf ⟨52965,8,(.group 10 9 false)⟩))
(.branch 52981
(.leaf ⟨52973,8,(.group 10 10 false)⟩)
(.leaf ⟨52981,8,(.group 10 11 false)⟩)))
(.branch 53005
(.branch 52997
(.leaf ⟨52989,8,(.group 10 12 false)⟩)
(.leaf ⟨52997,8,(.group 10 13 false)⟩))
(.branch 53013
(.leaf ⟨53005,8,(.group 10 14 false)⟩)
(.leaf ⟨53013,8,(.group 10 15 false)⟩))))
(.branch 53053
(.branch 53037
(.branch 53029
(.leaf ⟨53021,8,(.group 10 16 false)⟩)
(.leaf ⟨53029,8,(.group 10 17 false)⟩))
(.branch 53045
(.leaf ⟨53037,8,(.group 10 18 false)⟩)
(.leaf ⟨53045,8,(.group 10 19 false)⟩)))
(.branch 53069
(.branch 53061
(.leaf ⟨53053,8,(.group 10 20 false)⟩)
(.leaf ⟨53061,8,(.group 10 21 false)⟩))
(.branch 53077
(.leaf ⟨53069,8,(.group 10 22 false)⟩)
(.leaf ⟨53077,9,(.group 0 18 false)⟩))))))
(.branch 53230
(.branch 53158
(.branch 53122
(.branch 53104
(.branch 53095
(.leaf ⟨53086,9,(.group 0 19 false)⟩)
(.leaf ⟨53095,9,(.group 0 20 false)⟩))
(.branch 53113
(.leaf ⟨53104,9,(.group 0 21 false)⟩)
(.leaf ⟨53113,9,(.group 0 22 false)⟩)))
(.branch 53140
(.branch 53131
(.leaf ⟨53122,9,(.group 0 23 false)⟩)
(.leaf ⟨53131,9,(.group 0 24 false)⟩))
(.branch 53149
(.leaf ⟨53140,9,(.group 0 25 false)⟩)
(.leaf ⟨53149,9,(.group 0 26 false)⟩))))
(.branch 53194
(.branch 53176
(.branch 53167
(.leaf ⟨53158,9,(.group 0 27 false)⟩)
(.leaf ⟨53167,9,(.group 0 28 false)⟩))
(.branch 53185
(.leaf ⟨53176,9,(.group 0 29 false)⟩)
(.leaf ⟨53185,9,(.group 0 30 false)⟩)))
(.branch 53212
(.branch 53203
(.leaf ⟨53194,9,(.group 0 31 false)⟩)
(.leaf ⟨53203,9,(.group 0 32 false)⟩))
(.branch 53221
(.leaf ⟨53212,9,(.group 0 33 false)⟩)
(.leaf ⟨53221,9,(.group 0 34 false)⟩)))))
(.branch 53302
(.branch 53266
(.branch 53248
(.branch 53239
(.leaf ⟨53230,9,(.group 0 35 false)⟩)
(.leaf ⟨53239,9,(.group 0 36 false)⟩))
(.branch 53257
(.leaf ⟨53248,9,(.group 0 37 false)⟩)
(.leaf ⟨53257,9,(.group 1 4 false)⟩)))
(.branch 53284
(.branch 53275
(.leaf ⟨53266,9,(.group 1 5 false)⟩)
(.leaf ⟨53275,9,(.group 1 6 false)⟩))
(.branch 53293
(.leaf ⟨53284,9,(.group 1 7 false)⟩)
(.leaf ⟨53293,9,(.group 1 8 false)⟩))))
(.branch 53338
(.branch 53320
(.branch 53311
(.leaf ⟨53302,9,(.group 1 9 false)⟩)
(.leaf ⟨53311,9,(.group 2 4 false)⟩))
(.branch 53329
(.leaf ⟨53320,9,(.group 2 5 false)⟩)
(.leaf ⟨53329,9,(.group 2 6 false)⟩)))
(.branch 53356
(.branch 53347
(.leaf ⟨53338,9,(.group 2 7 false)⟩)
(.leaf ⟨53347,9,(.group 2 8 false)⟩))
(.branch 53365
(.leaf ⟨53356,9,(.group 2 9 false)⟩)
(.leaf ⟨53365,9,(.group 3 4 false)⟩)))))))

theorem tree48_checked : tree48.check 52829 53374 = true := by decide +kernel

def tree49 : Tree := (.branch 53662
(.branch 53518
(.branch 53446
(.branch 53410
(.branch 53392
(.branch 53383
(.leaf ⟨53374,9,(.group 3 5 false)⟩)
(.leaf ⟨53383,9,(.group 3 6 false)⟩))
(.branch 53401
(.leaf ⟨53392,9,(.group 3 7 false)⟩)
(.leaf ⟨53401,9,(.group 3 8 false)⟩)))
(.branch 53428
(.branch 53419
(.leaf ⟨53410,9,(.group 3 9 false)⟩)
(.leaf ⟨53419,9,(.group 4 4 false)⟩))
(.branch 53437
(.leaf ⟨53428,9,(.group 4 5 false)⟩)
(.leaf ⟨53437,9,(.group 4 6 false)⟩))))
(.branch 53482
(.branch 53464
(.branch 53455
(.leaf ⟨53446,9,(.group 4 7 false)⟩)
(.leaf ⟨53455,9,(.group 4 8 false)⟩))
(.branch 53473
(.leaf ⟨53464,9,(.group 4 9 false)⟩)
(.leaf ⟨53473,9,(.group 5 509 false)⟩)))
(.branch 53500
(.branch 53491
(.leaf ⟨53482,9,(.group 5 510 false)⟩)
(.leaf ⟨53491,9,(.group 5 511 false)⟩))
(.branch 53509
(.leaf ⟨53500,9,(.group 5 512 false)⟩)
(.leaf ⟨53509,9,(.group 5 513 false)⟩)))))
(.branch 53590
(.branch 53554
(.branch 53536
(.branch 53527
(.leaf ⟨53518,9,(.group 5 514 false)⟩)
(.leaf ⟨53527,9,(.group 5 515 false)⟩))
(.branch 53545
(.leaf ⟨53536,9,(.group 5 516 false)⟩)
(.leaf ⟨53545,9,(.group 5 517 false)⟩)))
(.branch 53572
(.branch 53563
(.leaf ⟨53554,9,(.group 5 518 false)⟩)
(.leaf ⟨53563,9,(.group 5 519 false)⟩))
(.branch 53581
(.leaf ⟨53572,9,(.group 5 520 false)⟩)
(.leaf ⟨53581,9,(.group 5 521 false)⟩))))
(.branch 53626
(.branch 53608
(.branch 53599
(.leaf ⟨53590,9,(.group 5 522 false)⟩)
(.leaf ⟨53599,9,(.group 5 523 false)⟩))
(.branch 53617
(.leaf ⟨53608,9,(.group 5 524 false)⟩)
(.leaf ⟨53617,9,(.group 5 525 false)⟩)))
(.branch 53644
(.branch 53635
(.leaf ⟨53626,9,(.group 5 526 false)⟩)
(.leaf ⟨53635,9,(.group 5 527 false)⟩))
(.branch 53653
(.leaf ⟨53644,9,(.group 5 528 false)⟩)
(.leaf ⟨53653,9,(.group 6 17 false)⟩))))))
(.branch 53806
(.branch 53734
(.branch 53698
(.branch 53680
(.branch 53671
(.leaf ⟨53662,9,(.group 6 18 false)⟩)
(.leaf ⟨53671,9,(.group 6 19 false)⟩))
(.branch 53689
(.leaf ⟨53680,9,(.group 6 20 false)⟩)
(.leaf ⟨53689,9,(.group 6 21 false)⟩)))
(.branch 53716
(.branch 53707
(.leaf ⟨53698,9,(.group 6 22 false)⟩)
(.leaf ⟨53707,9,(.group 6 23 false)⟩))
(.branch 53725
(.leaf ⟨53716,9,(.group 6 24 false)⟩)
(.leaf ⟨53725,9,(.group 6 25 false)⟩))))
(.branch 53770
(.branch 53752
(.branch 53743
(.leaf ⟨53734,9,(.group 6 26 false)⟩)
(.leaf ⟨53743,9,(.group 6 27 false)⟩))
(.branch 53761
(.leaf ⟨53752,9,(.group 6 28 false)⟩)
(.leaf ⟨53761,9,(.group 6 29 false)⟩)))
(.branch 53788
(.branch 53779
(.leaf ⟨53770,9,(.group 6 30 false)⟩)
(.leaf ⟨53779,9,(.group 6 31 false)⟩))
(.branch 53797
(.leaf ⟨53788,9,(.group 6 32 false)⟩)
(.leaf ⟨53797,9,(.group 6 33 false)⟩)))))
(.branch 53878
(.branch 53842
(.branch 53824
(.branch 53815
(.leaf ⟨53806,9,(.group 7 7 false)⟩)
(.leaf ⟨53815,9,(.group 7 8 false)⟩))
(.branch 53833
(.leaf ⟨53824,9,(.group 7 9 false)⟩)
(.leaf ⟨53833,9,(.group 7 10 false)⟩)))
(.branch 53860
(.branch 53851
(.leaf ⟨53842,9,(.group 7 11 false)⟩)
(.leaf ⟨53851,9,(.group 7 12 false)⟩))
(.branch 53869
(.leaf ⟨53860,9,(.group 7 13 false)⟩)
(.leaf ⟨53869,9,(.group 7 14 false)⟩))))
(.branch 53914
(.branch 53896
(.branch 53887
(.leaf ⟨53878,9,(.group 7 15 false)⟩)
(.leaf ⟨53887,9,(.group 7 16 false)⟩))
(.branch 53905
(.leaf ⟨53896,9,(.group 7 17 false)⟩)
(.leaf ⟨53905,9,(.group 7 18 false)⟩)))
(.branch 53932
(.branch 53923
(.leaf ⟨53914,9,(.group 7 19 false)⟩)
(.leaf ⟨53923,9,(.group 7 20 false)⟩))
(.branch 53941
(.leaf ⟨53932,9,(.group 8 27 false)⟩)
(.leaf ⟨53941,9,(.group 8 28 false)⟩)))))))

theorem tree49_checked : tree49.check 53374 53950 = true := by decide +kernel

def tree50 : Tree := (.branch 54238
(.branch 54094
(.branch 54022
(.branch 53986
(.branch 53968
(.branch 53959
(.leaf ⟨53950,9,(.group 8 29 false)⟩)
(.leaf ⟨53959,9,(.group 8 30 false)⟩))
(.branch 53977
(.leaf ⟨53968,9,(.group 8 31 false)⟩)
(.leaf ⟨53977,9,(.group 8 32 false)⟩)))
(.branch 54004
(.branch 53995
(.leaf ⟨53986,9,(.group 8 33 false)⟩)
(.leaf ⟨53995,9,(.group 8 34 false)⟩))
(.branch 54013
(.leaf ⟨54004,9,(.group 8 35 false)⟩)
(.leaf ⟨54013,9,(.group 8 36 false)⟩))))
(.branch 54058
(.branch 54040
(.branch 54031
(.leaf ⟨54022,9,(.group 8 37 false)⟩)
(.leaf ⟨54031,9,(.group 8 38 false)⟩))
(.branch 54049
(.leaf ⟨54040,9,(.group 8 39 false)⟩)
(.leaf ⟨54049,9,(.group 8 40 false)⟩)))
(.branch 54076
(.branch 54067
(.leaf ⟨54058,9,(.group 8 41 false)⟩)
(.leaf ⟨54067,9,(.group 8 42 false)⟩))
(.branch 54085
(.leaf ⟨54076,9,(.group 8 43 false)⟩)
(.leaf ⟨54085,9,(.group 8 44 false)⟩)))))
(.branch 54166
(.branch 54130
(.branch 54112
(.branch 54103
(.leaf ⟨54094,9,(.group 8 45 false)⟩)
(.leaf ⟨54103,9,(.group 8 46 false)⟩))
(.branch 54121
(.leaf ⟨54112,9,(.group 8 47 false)⟩)
(.leaf ⟨54121,9,(.group 8 48 false)⟩)))
(.branch 54148
(.branch 54139
(.leaf ⟨54130,9,(.group 8 49 false)⟩)
(.leaf ⟨54139,9,(.group 8 50 false)⟩))
(.branch 54157
(.leaf ⟨54148,9,(.group 8 51 false)⟩)
(.leaf ⟨54157,9,(.group 8 52 false)⟩))))
(.branch 54202
(.branch 54184
(.branch 54175
(.leaf ⟨54166,9,(.group 8 53 false)⟩)
(.leaf ⟨54175,9,(.group 8 54 false)⟩))
(.branch 54193
(.leaf ⟨54184,9,(.group 8 55 false)⟩)
(.leaf ⟨54193,9,(.group 8 56 false)⟩)))
(.branch 54220
(.branch 54211
(.leaf ⟨54202,9,(.group 9 24 false)⟩)
(.leaf ⟨54211,9,(.group 9 25 false)⟩))
(.branch 54229
(.leaf ⟨54220,9,(.group 9 26 false)⟩)
(.leaf ⟨54229,9,(.group 9 27 false)⟩))))))
(.branch 54383
(.branch 54310
(.branch 54274
(.branch 54256
(.branch 54247
(.leaf ⟨54238,9,(.group 9 28 false)⟩)
(.leaf ⟨54247,9,(.group 9 29 false)⟩))
(.branch 54265
(.leaf ⟨54256,9,(.group 9 30 false)⟩)
(.leaf ⟨54265,9,(.group 9 31 false)⟩)))
(.branch 54292
(.branch 54283
(.leaf ⟨54274,9,(.group 9 32 false)⟩)
(.leaf ⟨54283,9,(.group 10 27 false)⟩))
(.branch 54301
(.leaf ⟨54292,9,(.group 10 28 false)⟩)
(.leaf ⟨54301,9,(.group 10 29 false)⟩))))
(.branch 54346
(.branch 54328
(.branch 54319
(.leaf ⟨54310,9,(.group 10 30 false)⟩)
(.leaf ⟨54319,9,(.group 10 31 false)⟩))
(.branch 54337
(.leaf ⟨54328,9,(.group 10 32 false)⟩)
(.leaf ⟨54337,9,(.group 10 33 false)⟩)))
(.branch 54364
(.branch 54355
(.leaf ⟨54346,9,(.group 10 34 false)⟩)
(.leaf ⟨54355,9,(.group 10 35 false)⟩))
(.branch 54373
(.leaf ⟨54364,9,(.group 10 36 false)⟩)
(.leaf ⟨54373,10,(.group 0 38 false)⟩)))))
(.branch 54463
(.branch 54423
(.branch 54403
(.branch 54393
(.leaf ⟨54383,10,(.group 0 39 false)⟩)
(.leaf ⟨54393,10,(.group 0 40 false)⟩))
(.branch 54413
(.leaf ⟨54403,10,(.group 0 41 false)⟩)
(.leaf ⟨54413,10,(.group 0 42 false)⟩)))
(.branch 54443
(.branch 54433
(.leaf ⟨54423,10,(.group 0 43 false)⟩)
(.leaf ⟨54433,10,(.group 0 44 false)⟩))
(.branch 54453
(.leaf ⟨54443,10,(.group 0 45 false)⟩)
(.leaf ⟨54453,10,(.group 0 46 false)⟩))))
(.branch 54503
(.branch 54483
(.branch 54473
(.leaf ⟨54463,10,(.group 0 47 false)⟩)
(.leaf ⟨54473,10,(.group 0 48 false)⟩))
(.branch 54493
(.leaf ⟨54483,10,(.group 0 49 false)⟩)
(.leaf ⟨54493,10,(.group 0 50 false)⟩)))
(.branch 54523
(.branch 54513
(.leaf ⟨54503,10,(.group 0 51 false)⟩)
(.leaf ⟨54513,10,(.group 0 52 false)⟩))
(.branch 54533
(.leaf ⟨54523,10,(.group 0 53 false)⟩)
(.leaf ⟨54533,10,(.group 0 54 false)⟩)))))))

theorem tree50_checked : tree50.check 53950 54543 = true := by decide +kernel

def tree51 : Tree := (.branch 54863
(.branch 54703
(.branch 54623
(.branch 54583
(.branch 54563
(.branch 54553
(.leaf ⟨54543,10,(.group 0 55 false)⟩)
(.leaf ⟨54553,10,(.group 0 56 false)⟩))
(.branch 54573
(.leaf ⟨54563,10,(.group 0 57 false)⟩)
(.leaf ⟨54573,10,(.group 0 58 false)⟩)))
(.branch 54603
(.branch 54593
(.leaf ⟨54583,10,(.group 0 59 false)⟩)
(.leaf ⟨54593,10,(.group 0 60 false)⟩))
(.branch 54613
(.leaf ⟨54603,10,(.group 0 61 false)⟩)
(.leaf ⟨54613,10,(.group 0 62 false)⟩))))
(.branch 54663
(.branch 54643
(.branch 54633
(.leaf ⟨54623,10,(.group 0 63 false)⟩)
(.leaf ⟨54633,10,(.group 0 64 false)⟩))
(.branch 54653
(.leaf ⟨54643,10,(.group 0 65 false)⟩)
(.leaf ⟨54653,10,(.group 0 66 false)⟩)))
(.branch 54683
(.branch 54673
(.leaf ⟨54663,10,(.group 0 67 false)⟩)
(.leaf ⟨54673,10,(.group 1 10 false)⟩))
(.branch 54693
(.leaf ⟨54683,10,(.group 1 11 false)⟩)
(.leaf ⟨54693,10,(.group 1 12 false)⟩)))))
(.branch 54783
(.branch 54743
(.branch 54723
(.branch 54713
(.leaf ⟨54703,10,(.group 1 13 false)⟩)
(.leaf ⟨54713,10,(.group 1 14 false)⟩))
(.branch 54733
(.leaf ⟨54723,10,(.group 1 15 false)⟩)
(.leaf ⟨54733,10,(.group 1 16 false)⟩)))
(.branch 54763
(.branch 54753
(.leaf ⟨54743,10,(.group 1 17 false)⟩)
(.leaf ⟨54753,10,(.group 1 18 false)⟩))
(.branch 54773
(.leaf ⟨54763,10,(.group 1 19 false)⟩)
(.leaf ⟨54773,10,(.group 2 10 false)⟩))))
(.branch 54823
(.branch 54803
(.branch 54793
(.leaf ⟨54783,10,(.group 2 11 false)⟩)
(.leaf ⟨54793,10,(.group 2 12 false)⟩))
(.branch 54813
(.leaf ⟨54803,10,(.group 2 13 false)⟩)
(.leaf ⟨54813,10,(.group 2 14 false)⟩)))
(.branch 54843
(.branch 54833
(.leaf ⟨54823,10,(.group 2 15 false)⟩)
(.leaf ⟨54833,10,(.group 2 16 false)⟩))
(.branch 54853
(.leaf ⟨54843,10,(.group 2 17 false)⟩)
(.leaf ⟨54853,10,(.group 2 18 false)⟩))))))
(.branch 55023
(.branch 54943
(.branch 54903
(.branch 54883
(.branch 54873
(.leaf ⟨54863,10,(.group 2 19 false)⟩)
(.leaf ⟨54873,10,(.group 3 10 false)⟩))
(.branch 54893
(.leaf ⟨54883,10,(.group 3 11 false)⟩)
(.leaf ⟨54893,10,(.group 3 12 false)⟩)))
(.branch 54923
(.branch 54913
(.leaf ⟨54903,10,(.group 3 13 false)⟩)
(.leaf ⟨54913,10,(.group 3 14 false)⟩))
(.branch 54933
(.leaf ⟨54923,10,(.group 3 15 false)⟩)
(.leaf ⟨54933,10,(.group 3 16 false)⟩))))
(.branch 54983
(.branch 54963
(.branch 54953
(.leaf ⟨54943,10,(.group 3 17 false)⟩)
(.leaf ⟨54953,10,(.group 3 18 false)⟩))
(.branch 54973
(.leaf ⟨54963,10,(.group 3 19 false)⟩)
(.leaf ⟨54973,10,(.group 4 10 false)⟩)))
(.branch 55003
(.branch 54993
(.leaf ⟨54983,10,(.group 4 11 false)⟩)
(.leaf ⟨54993,10,(.group 4 12 false)⟩))
(.branch 55013
(.leaf ⟨55003,10,(.group 4 13 false)⟩)
(.leaf ⟨55013,10,(.group 4 14 false)⟩)))))
(.branch 55103
(.branch 55063
(.branch 55043
(.branch 55033
(.leaf ⟨55023,10,(.group 4 15 false)⟩)
(.leaf ⟨55033,10,(.group 4 16 false)⟩))
(.branch 55053
(.leaf ⟨55043,10,(.group 4 17 false)⟩)
(.leaf ⟨55053,10,(.group 4 18 false)⟩)))
(.branch 55083
(.branch 55073
(.leaf ⟨55063,10,(.group 4 19 false)⟩)
(.leaf ⟨55073,10,(.group 5 529 false)⟩))
(.branch 55093
(.leaf ⟨55083,10,(.group 5 530 false)⟩)
(.leaf ⟨55093,10,(.group 5 531 false)⟩))))
(.branch 55143
(.branch 55123
(.branch 55113
(.leaf ⟨55103,10,(.group 5 532 false)⟩)
(.leaf ⟨55113,10,(.group 5 533 false)⟩))
(.branch 55133
(.leaf ⟨55123,10,(.group 5 534 false)⟩)
(.leaf ⟨55133,10,(.group 5 535 false)⟩)))
(.branch 55163
(.branch 55153
(.leaf ⟨55143,10,(.group 5 536 false)⟩)
(.leaf ⟨55153,10,(.group 5 537 false)⟩))
(.branch 55173
(.leaf ⟨55163,10,(.group 5 538 false)⟩)
(.leaf ⟨55173,10,(.group 5 539 false)⟩)))))))

theorem tree51_checked : tree51.check 54543 55183 = true := by decide +kernel

def tree52 : Tree := (.branch 55503
(.branch 55343
(.branch 55263
(.branch 55223
(.branch 55203
(.branch 55193
(.leaf ⟨55183,10,(.group 5 540 false)⟩)
(.leaf ⟨55193,10,(.group 5 541 false)⟩))
(.branch 55213
(.leaf ⟨55203,10,(.group 5 542 false)⟩)
(.leaf ⟨55213,10,(.group 5 543 false)⟩)))
(.branch 55243
(.branch 55233
(.leaf ⟨55223,10,(.group 5 544 false)⟩)
(.leaf ⟨55233,10,(.group 5 545 false)⟩))
(.branch 55253
(.leaf ⟨55243,10,(.group 5 546 false)⟩)
(.leaf ⟨55253,10,(.group 5 547 false)⟩))))
(.branch 55303
(.branch 55283
(.branch 55273
(.leaf ⟨55263,10,(.group 5 548 false)⟩)
(.leaf ⟨55273,10,(.group 5 549 false)⟩))
(.branch 55293
(.leaf ⟨55283,10,(.group 5 550 false)⟩)
(.leaf ⟨55293,10,(.group 5 551 false)⟩)))
(.branch 55323
(.branch 55313
(.leaf ⟨55303,10,(.group 5 552 false)⟩)
(.leaf ⟨55313,10,(.group 5 553 false)⟩))
(.branch 55333
(.leaf ⟨55323,10,(.group 5 554 false)⟩)
(.leaf ⟨55333,10,(.group 5 555 false)⟩)))))
(.branch 55423
(.branch 55383
(.branch 55363
(.branch 55353
(.leaf ⟨55343,10,(.group 5 556 false)⟩)
(.leaf ⟨55353,10,(.group 5 557 false)⟩))
(.branch 55373
(.leaf ⟨55363,10,(.group 5 558 false)⟩)
(.leaf ⟨55373,10,(.group 5 559 false)⟩)))
(.branch 55403
(.branch 55393
(.leaf ⟨55383,10,(.group 5 560 false)⟩)
(.leaf ⟨55393,10,(.group 5 561 false)⟩))
(.branch 55413
(.leaf ⟨55403,10,(.group 5 562 false)⟩)
(.leaf ⟨55413,10,(.group 5 563 false)⟩))))
(.branch 55463
(.branch 55443
(.branch 55433
(.leaf ⟨55423,10,(.group 5 564 false)⟩)
(.leaf ⟨55433,10,(.group 5 565 false)⟩))
(.branch 55453
(.leaf ⟨55443,10,(.group 6 34 false)⟩)
(.leaf ⟨55453,10,(.group 6 35 false)⟩)))
(.branch 55483
(.branch 55473
(.leaf ⟨55463,10,(.group 6 36 false)⟩)
(.leaf ⟨55473,10,(.group 6 37 false)⟩))
(.branch 55493
(.leaf ⟨55483,10,(.group 6 38 false)⟩)
(.leaf ⟨55493,10,(.group 6 39 false)⟩))))))
(.branch 55663
(.branch 55583
(.branch 55543
(.branch 55523
(.branch 55513
(.leaf ⟨55503,10,(.group 6 40 false)⟩)
(.leaf ⟨55513,10,(.group 6 41 false)⟩))
(.branch 55533
(.leaf ⟨55523,10,(.group 6 42 false)⟩)
(.leaf ⟨55533,10,(.group 6 43 false)⟩)))
(.branch 55563
(.branch 55553
(.leaf ⟨55543,10,(.group 6 44 false)⟩)
(.leaf ⟨55553,10,(.group 6 45 false)⟩))
(.branch 55573
(.leaf ⟨55563,10,(.group 6 46 false)⟩)
(.leaf ⟨55573,10,(.group 6 47 false)⟩))))
(.branch 55623
(.branch 55603
(.branch 55593
(.leaf ⟨55583,10,(.group 6 48 false)⟩)
(.leaf ⟨55593,10,(.group 6 49 false)⟩))
(.branch 55613
(.leaf ⟨55603,10,(.group 6 50 false)⟩)
(.leaf ⟨55613,10,(.group 6 51 false)⟩)))
(.branch 55643
(.branch 55633
(.leaf ⟨55623,10,(.group 6 52 false)⟩)
(.leaf ⟨55633,10,(.group 6 53 false)⟩))
(.branch 55653
(.leaf ⟨55643,10,(.group 6 54 false)⟩)
(.leaf ⟨55653,10,(.group 6 55 false)⟩)))))
(.branch 55743
(.branch 55703
(.branch 55683
(.branch 55673
(.leaf ⟨55663,10,(.group 6 56 false)⟩)
(.leaf ⟨55673,10,(.group 6 57 false)⟩))
(.branch 55693
(.leaf ⟨55683,10,(.group 6 58 false)⟩)
(.leaf ⟨55693,10,(.group 6 59 false)⟩)))
(.branch 55723
(.branch 55713
(.leaf ⟨55703,10,(.group 6 60 false)⟩)
(.leaf ⟨55713,10,(.group 6 61 false)⟩))
(.branch 55733
(.leaf ⟨55723,10,(.group 6 62 false)⟩)
(.leaf ⟨55733,10,(.group 6 63 false)⟩))))
(.branch 55783
(.branch 55763
(.branch 55753
(.leaf ⟨55743,10,(.group 7 21 false)⟩)
(.leaf ⟨55753,10,(.group 7 22 false)⟩))
(.branch 55773
(.leaf ⟨55763,10,(.group 7 23 false)⟩)
(.leaf ⟨55773,10,(.group 7 24 false)⟩)))
(.branch 55803
(.branch 55793
(.leaf ⟨55783,10,(.group 7 25 false)⟩)
(.leaf ⟨55793,10,(.group 7 26 false)⟩))
(.branch 55813
(.leaf ⟨55803,10,(.group 7 27 false)⟩)
(.leaf ⟨55813,10,(.group 7 28 false)⟩)))))))

theorem tree52_checked : tree52.check 55183 55823 = true := by decide +kernel

def tree53 : Tree := (.branch 56143
(.branch 55983
(.branch 55903
(.branch 55863
(.branch 55843
(.branch 55833
(.leaf ⟨55823,10,(.group 7 29 false)⟩)
(.leaf ⟨55833,10,(.group 7 30 false)⟩))
(.branch 55853
(.leaf ⟨55843,10,(.group 8 60 false)⟩)
(.leaf ⟨55853,10,(.group 8 61 false)⟩)))
(.branch 55883
(.branch 55873
(.leaf ⟨55863,10,(.group 8 62 false)⟩)
(.leaf ⟨55873,10,(.group 8 63 false)⟩))
(.branch 55893
(.leaf ⟨55883,10,(.group 8 64 false)⟩)
(.leaf ⟨55893,10,(.group 8 65 false)⟩))))
(.branch 55943
(.branch 55923
(.branch 55913
(.leaf ⟨55903,10,(.group 8 66 false)⟩)
(.leaf ⟨55913,10,(.group 8 67 false)⟩))
(.branch 55933
(.leaf ⟨55923,10,(.group 8 68 false)⟩)
(.leaf ⟨55933,10,(.group 8 69 false)⟩)))
(.branch 55963
(.branch 55953
(.leaf ⟨55943,10,(.group 8 70 false)⟩)
(.leaf ⟨55953,10,(.group 8 71 false)⟩))
(.branch 55973
(.leaf ⟨55963,10,(.group 9 36 false)⟩)
(.leaf ⟨55973,10,(.group 9 37 false)⟩)))))
(.branch 56063
(.branch 56023
(.branch 56003
(.branch 55993
(.leaf ⟨55983,10,(.group 9 38 false)⟩)
(.leaf ⟨55993,10,(.group 9 39 false)⟩))
(.branch 56013
(.leaf ⟨56003,10,(.group 9 40 false)⟩)
(.leaf ⟨56013,10,(.group 9 41 false)⟩)))
(.branch 56043
(.branch 56033
(.leaf ⟨56023,10,(.group 9 42 false)⟩)
(.leaf ⟨56033,10,(.group 9 43 false)⟩))
(.branch 56053
(.leaf ⟨56043,10,(.group 9 44 false)⟩)
(.leaf ⟨56053,10,(.group 9 45 false)⟩))))
(.branch 56103
(.branch 56083
(.branch 56073
(.leaf ⟨56063,10,(.group 9 46 false)⟩)
(.leaf ⟨56073,10,(.group 9 47 false)⟩))
(.branch 56093
(.leaf ⟨56083,10,(.group 9 48 false)⟩)
(.leaf ⟨56093,10,(.group 9 49 false)⟩)))
(.branch 56123
(.branch 56113
(.leaf ⟨56103,10,(.group 9 50 false)⟩)
(.leaf ⟨56113,10,(.group 9 51 false)⟩))
(.branch 56133
(.leaf ⟨56123,10,(.group 9 52 false)⟩)
(.leaf ⟨56133,10,(.group 9 53 false)⟩))))))
(.branch 56310
(.branch 56223
(.branch 56183
(.branch 56163
(.branch 56153
(.leaf ⟨56143,10,(.group 9 54 false)⟩)
(.leaf ⟨56153,10,(.group 9 55 false)⟩))
(.branch 56173
(.leaf ⟨56163,10,(.group 9 56 false)⟩)
(.leaf ⟨56173,10,(.group 9 57 false)⟩)))
(.branch 56203
(.branch 56193
(.leaf ⟨56183,10,(.group 9 58 false)⟩)
(.leaf ⟨56193,10,(.group 9 59 false)⟩))
(.branch 56213
(.leaf ⟨56203,10,(.group 10 39 false)⟩)
(.leaf ⟨56213,10,(.group 10 40 false)⟩))))
(.branch 56266
(.branch 56244
(.branch 56233
(.leaf ⟨56223,10,(.group 10 41 false)⟩)
(.leaf ⟨56233,11,(.group 0 68 false)⟩))
(.branch 56255
(.leaf ⟨56244,11,(.group 0 69 false)⟩)
(.leaf ⟨56255,11,(.group 0 70 false)⟩)))
(.branch 56288
(.branch 56277
(.leaf ⟨56266,11,(.group 0 71 false)⟩)
(.leaf ⟨56277,11,(.group 0 72 false)⟩))
(.branch 56299
(.leaf ⟨56288,11,(.group 0 73 false)⟩)
(.leaf ⟨56299,11,(.group 0 74 false)⟩)))))
(.branch 56398
(.branch 56354
(.branch 56332
(.branch 56321
(.leaf ⟨56310,11,(.group 0 75 false)⟩)
(.leaf ⟨56321,11,(.group 0 76 false)⟩))
(.branch 56343
(.leaf ⟨56332,11,(.group 0 77 false)⟩)
(.leaf ⟨56343,11,(.group 0 78 false)⟩)))
(.branch 56376
(.branch 56365
(.leaf ⟨56354,11,(.group 0 79 false)⟩)
(.leaf ⟨56365,11,(.group 0 80 false)⟩))
(.branch 56387
(.leaf ⟨56376,11,(.group 0 81 false)⟩)
(.leaf ⟨56387,11,(.group 0 82 false)⟩))))
(.branch 56442
(.branch 56420
(.branch 56409
(.leaf ⟨56398,11,(.group 0 83 false)⟩)
(.leaf ⟨56409,11,(.group 0 84 false)⟩))
(.branch 56431
(.leaf ⟨56420,11,(.group 0 85 false)⟩)
(.leaf ⟨56431,11,(.group 0 86 false)⟩)))
(.branch 56464
(.branch 56453
(.leaf ⟨56442,11,(.group 0 87 false)⟩)
(.leaf ⟨56453,11,(.group 0 88 false)⟩))
(.branch 56475
(.leaf ⟨56464,11,(.group 0 89 false)⟩)
(.leaf ⟨56475,11,(.group 0 90 false)⟩)))))))

theorem tree53_checked : tree53.check 55823 56486 = true := by decide +kernel

def tree54 : Tree := (.branch 56838
(.branch 56662
(.branch 56574
(.branch 56530
(.branch 56508
(.branch 56497
(.leaf ⟨56486,11,(.group 0 91 false)⟩)
(.leaf ⟨56497,11,(.group 0 92 false)⟩))
(.branch 56519
(.leaf ⟨56508,11,(.group 0 93 false)⟩)
(.leaf ⟨56519,11,(.group 0 94 false)⟩)))
(.branch 56552
(.branch 56541
(.leaf ⟨56530,11,(.group 0 95 false)⟩)
(.leaf ⟨56541,11,(.group 0 96 false)⟩))
(.branch 56563
(.leaf ⟨56552,11,(.group 0 97 false)⟩)
(.leaf ⟨56563,11,(.group 0 98 false)⟩))))
(.branch 56618
(.branch 56596
(.branch 56585
(.leaf ⟨56574,11,(.group 0 99 false)⟩)
(.leaf ⟨56585,11,(.group 0 100 false)⟩))
(.branch 56607
(.leaf ⟨56596,11,(.group 0 101 false)⟩)
(.leaf ⟨56607,11,(.group 0 102 false)⟩)))
(.branch 56640
(.branch 56629
(.leaf ⟨56618,11,(.group 0 103 false)⟩)
(.leaf ⟨56629,11,(.group 0 104 false)⟩))
(.branch 56651
(.leaf ⟨56640,11,(.group 0 105 false)⟩)
(.leaf ⟨56651,11,(.group 0 106 false)⟩)))))
(.branch 56750
(.branch 56706
(.branch 56684
(.branch 56673
(.leaf ⟨56662,11,(.group 0 107 false)⟩)
(.leaf ⟨56673,11,(.group 0 108 false)⟩))
(.branch 56695
(.leaf ⟨56684,11,(.group 0 109 false)⟩)
(.leaf ⟨56695,11,(.group 1 20 false)⟩)))
(.branch 56728
(.branch 56717
(.leaf ⟨56706,11,(.group 1 21 false)⟩)
(.leaf ⟨56717,11,(.group 1 22 false)⟩))
(.branch 56739
(.leaf ⟨56728,11,(.group 1 23 false)⟩)
(.leaf ⟨56739,11,(.group 1 24 false)⟩))))
(.branch 56794
(.branch 56772
(.branch 56761
(.leaf ⟨56750,11,(.group 1 25 false)⟩)
(.leaf ⟨56761,11,(.group 1 26 false)⟩))
(.branch 56783
(.leaf ⟨56772,11,(.group 1 27 false)⟩)
(.leaf ⟨56783,11,(.group 1 28 false)⟩)))
(.branch 56816
(.branch 56805
(.leaf ⟨56794,11,(.group 1 29 false)⟩)
(.leaf ⟨56805,11,(.group 1 30 false)⟩))
(.branch 56827
(.leaf ⟨56816,11,(.group 1 31 false)⟩)
(.leaf ⟨56827,11,(.group 1 32 false)⟩))))))
(.branch 57014
(.branch 56926
(.branch 56882
(.branch 56860
(.branch 56849
(.leaf ⟨56838,11,(.group 1 33 false)⟩)
(.leaf ⟨56849,11,(.group 1 34 false)⟩))
(.branch 56871
(.leaf ⟨56860,11,(.group 2 20 false)⟩)
(.leaf ⟨56871,11,(.group 2 21 false)⟩)))
(.branch 56904
(.branch 56893
(.leaf ⟨56882,11,(.group 2 22 false)⟩)
(.leaf ⟨56893,11,(.group 2 23 false)⟩))
(.branch 56915
(.leaf ⟨56904,11,(.group 2 24 false)⟩)
(.leaf ⟨56915,11,(.group 2 25 false)⟩))))
(.branch 56970
(.branch 56948
(.branch 56937
(.leaf ⟨56926,11,(.group 2 26 false)⟩)
(.leaf ⟨56937,11,(.group 2 27 false)⟩))
(.branch 56959
(.leaf ⟨56948,11,(.group 2 28 false)⟩)
(.leaf ⟨56959,11,(.group 2 29 false)⟩)))
(.branch 56992
(.branch 56981
(.leaf ⟨56970,11,(.group 2 30 false)⟩)
(.leaf ⟨56981,11,(.group 2 31 false)⟩))
(.branch 57003
(.leaf ⟨56992,11,(.group 2 32 false)⟩)
(.leaf ⟨57003,11,(.group 2 33 false)⟩)))))
(.branch 57102
(.branch 57058
(.branch 57036
(.branch 57025
(.leaf ⟨57014,11,(.group 2 34 false)⟩)
(.leaf ⟨57025,11,(.group 3 20 false)⟩))
(.branch 57047
(.leaf ⟨57036,11,(.group 3 21 false)⟩)
(.leaf ⟨57047,11,(.group 3 22 false)⟩)))
(.branch 57080
(.branch 57069
(.leaf ⟨57058,11,(.group 3 23 false)⟩)
(.leaf ⟨57069,11,(.group 3 24 false)⟩))
(.branch 57091
(.leaf ⟨57080,11,(.group 3 25 false)⟩)
(.leaf ⟨57091,11,(.group 3 26 false)⟩))))
(.branch 57146
(.branch 57124
(.branch 57113
(.leaf ⟨57102,11,(.group 3 27 false)⟩)
(.leaf ⟨57113,11,(.group 3 28 false)⟩))
(.branch 57135
(.leaf ⟨57124,11,(.group 3 29 false)⟩)
(.leaf ⟨57135,11,(.group 3 30 false)⟩)))
(.branch 57168
(.branch 57157
(.leaf ⟨57146,11,(.group 3 31 false)⟩)
(.leaf ⟨57157,11,(.group 3 32 false)⟩))
(.branch 57179
(.leaf ⟨57168,11,(.group 3 33 false)⟩)
(.leaf ⟨57179,11,(.group 3 34 false)⟩)))))))

theorem tree54_checked : tree54.check 56486 57190 = true := by decide +kernel

def tree55 : Tree := (.branch 57542
(.branch 57366
(.branch 57278
(.branch 57234
(.branch 57212
(.branch 57201
(.leaf ⟨57190,11,(.group 4 20 false)⟩)
(.leaf ⟨57201,11,(.group 4 21 false)⟩))
(.branch 57223
(.leaf ⟨57212,11,(.group 4 22 false)⟩)
(.leaf ⟨57223,11,(.group 4 23 false)⟩)))
(.branch 57256
(.branch 57245
(.leaf ⟨57234,11,(.group 4 24 false)⟩)
(.leaf ⟨57245,11,(.group 4 25 false)⟩))
(.branch 57267
(.leaf ⟨57256,11,(.group 4 26 false)⟩)
(.leaf ⟨57267,11,(.group 4 27 false)⟩))))
(.branch 57322
(.branch 57300
(.branch 57289
(.leaf ⟨57278,11,(.group 4 28 false)⟩)
(.leaf ⟨57289,11,(.group 4 29 false)⟩))
(.branch 57311
(.leaf ⟨57300,11,(.group 4 30 false)⟩)
(.leaf ⟨57311,11,(.group 4 31 false)⟩)))
(.branch 57344
(.branch 57333
(.leaf ⟨57322,11,(.group 4 32 false)⟩)
(.leaf ⟨57333,11,(.group 4 33 false)⟩))
(.branch 57355
(.leaf ⟨57344,11,(.group 4 34 false)⟩)
(.leaf ⟨57355,11,(.group 5 566 false)⟩)))))
(.branch 57454
(.branch 57410
(.branch 57388
(.branch 57377
(.leaf ⟨57366,11,(.group 5 567 false)⟩)
(.leaf ⟨57377,11,(.group 5 568 false)⟩))
(.branch 57399
(.leaf ⟨57388,11,(.group 5 569 false)⟩)
(.leaf ⟨57399,11,(.group 5 570 false)⟩)))
(.branch 57432
(.branch 57421
(.leaf ⟨57410,11,(.group 5 571 false)⟩)
(.leaf ⟨57421,11,(.group 5 572 false)⟩))
(.branch 57443
(.leaf ⟨57432,11,(.group 5 573 false)⟩)
(.leaf ⟨57443,11,(.group 5 574 false)⟩))))
(.branch 57498
(.branch 57476
(.branch 57465
(.leaf ⟨57454,11,(.group 5 575 false)⟩)
(.leaf ⟨57465,11,(.group 5 576 false)⟩))
(.branch 57487
(.leaf ⟨57476,11,(.group 5 577 false)⟩)
(.leaf ⟨57487,11,(.group 5 578 false)⟩)))
(.branch 57520
(.branch 57509
(.leaf ⟨57498,11,(.group 5 579 false)⟩)
(.leaf ⟨57509,11,(.group 5 580 false)⟩))
(.branch 57531
(.leaf ⟨57520,11,(.group 5 581 false)⟩)
(.leaf ⟨57531,11,(.group 5 582 false)⟩))))))
(.branch 57718
(.branch 57630
(.branch 57586
(.branch 57564
(.branch 57553
(.leaf ⟨57542,11,(.group 5 583 false)⟩)
(.leaf ⟨57553,11,(.group 5 584 false)⟩))
(.branch 57575
(.leaf ⟨57564,11,(.group 5 585 false)⟩)
(.leaf ⟨57575,11,(.group 5 586 false)⟩)))
(.branch 57608
(.branch 57597
(.leaf ⟨57586,11,(.group 5 587 false)⟩)
(.leaf ⟨57597,11,(.group 5 588 false)⟩))
(.branch 57619
(.leaf ⟨57608,11,(.group 5 589 false)⟩)
(.leaf ⟨57619,11,(.group 5 590 false)⟩))))
(.branch 57674
(.branch 57652
(.branch 57641
(.leaf ⟨57630,11,(.group 5 591 false)⟩)
(.leaf ⟨57641,11,(.group 5 592 false)⟩))
(.branch 57663
(.leaf ⟨57652,11,(.group 5 593 false)⟩)
(.leaf ⟨57663,11,(.group 5 594 false)⟩)))
(.branch 57696
(.branch 57685
(.leaf ⟨57674,11,(.group 5 595 false)⟩)
(.leaf ⟨57685,11,(.group 5 596 false)⟩))
(.branch 57707
(.leaf ⟨57696,11,(.group 5 597 false)⟩)
(.leaf ⟨57707,11,(.group 5 598 false)⟩)))))
(.branch 57806
(.branch 57762
(.branch 57740
(.branch 57729
(.leaf ⟨57718,11,(.group 5 599 false)⟩)
(.leaf ⟨57729,11,(.group 5 600 false)⟩))
(.branch 57751
(.leaf ⟨57740,11,(.group 5 601 false)⟩)
(.leaf ⟨57751,11,(.group 5 602 false)⟩)))
(.branch 57784
(.branch 57773
(.leaf ⟨57762,11,(.group 5 603 false)⟩)
(.leaf ⟨57773,11,(.group 5 604 false)⟩))
(.branch 57795
(.leaf ⟨57784,11,(.group 5 605 false)⟩)
(.leaf ⟨57795,11,(.group 5 606 false)⟩))))
(.branch 57850
(.branch 57828
(.branch 57817
(.leaf ⟨57806,11,(.group 5 607 false)⟩)
(.leaf ⟨57817,11,(.group 5 608 false)⟩))
(.branch 57839
(.leaf ⟨57828,11,(.group 5 609 false)⟩)
(.leaf ⟨57839,11,(.group 5 610 false)⟩)))
(.branch 57872
(.branch 57861
(.leaf ⟨57850,11,(.group 5 611 false)⟩)
(.leaf ⟨57861,11,(.group 5 612 false)⟩))
(.branch 57883
(.leaf ⟨57872,11,(.group 5 613 false)⟩)
(.leaf ⟨57883,11,(.group 5 614 false)⟩)))))))

theorem tree55_checked : tree55.check 57190 57894 = true := by decide +kernel

def tree56 : Tree := (.branch 58246
(.branch 58070
(.branch 57982
(.branch 57938
(.branch 57916
(.branch 57905
(.leaf ⟨57894,11,(.group 5 615 false)⟩)
(.leaf ⟨57905,11,(.group 5 616 false)⟩))
(.branch 57927
(.leaf ⟨57916,11,(.group 5 617 false)⟩)
(.leaf ⟨57927,11,(.group 5 618 false)⟩)))
(.branch 57960
(.branch 57949
(.leaf ⟨57938,11,(.group 5 619 false)⟩)
(.leaf ⟨57949,11,(.group 5 620 false)⟩))
(.branch 57971
(.leaf ⟨57960,11,(.group 5 621 false)⟩)
(.leaf ⟨57971,11,(.group 6 64 false)⟩))))
(.branch 58026
(.branch 58004
(.branch 57993
(.leaf ⟨57982,11,(.group 6 65 false)⟩)
(.leaf ⟨57993,11,(.group 6 66 false)⟩))
(.branch 58015
(.leaf ⟨58004,11,(.group 6 67 false)⟩)
(.leaf ⟨58015,11,(.group 6 68 false)⟩)))
(.branch 58048
(.branch 58037
(.leaf ⟨58026,11,(.group 6 69 false)⟩)
(.leaf ⟨58037,11,(.group 6 70 false)⟩))
(.branch 58059
(.leaf ⟨58048,11,(.group 6 71 false)⟩)
(.leaf ⟨58059,11,(.group 6 72 false)⟩)))))
(.branch 58158
(.branch 58114
(.branch 58092
(.branch 58081
(.leaf ⟨58070,11,(.group 6 73 false)⟩)
(.leaf ⟨58081,11,(.group 6 74 false)⟩))
(.branch 58103
(.leaf ⟨58092,11,(.group 6 75 false)⟩)
(.leaf ⟨58103,11,(.group 6 76 false)⟩)))
(.branch 58136
(.branch 58125
(.leaf ⟨58114,11,(.group 6 77 false)⟩)
(.leaf ⟨58125,11,(.group 6 78 false)⟩))
(.branch 58147
(.leaf ⟨58136,11,(.group 6 79 false)⟩)
(.leaf ⟨58147,11,(.group 6 80 false)⟩))))
(.branch 58202
(.branch 58180
(.branch 58169
(.leaf ⟨58158,11,(.group 6 81 false)⟩)
(.leaf ⟨58169,11,(.group 6 82 false)⟩))
(.branch 58191
(.leaf ⟨58180,11,(.group 6 83 false)⟩)
(.leaf ⟨58191,11,(.group 6 84 false)⟩)))
(.branch 58224
(.branch 58213
(.leaf ⟨58202,11,(.group 6 85 false)⟩)
(.leaf ⟨58213,11,(.group 6 86 false)⟩))
(.branch 58235
(.leaf ⟨58224,11,(.group 6 87 false)⟩)
(.leaf ⟨58235,11,(.group 6 88 false)⟩))))))
(.branch 58422
(.branch 58334
(.branch 58290
(.branch 58268
(.branch 58257
(.leaf ⟨58246,11,(.group 6 89 false)⟩)
(.leaf ⟨58257,11,(.group 6 90 false)⟩))
(.branch 58279
(.leaf ⟨58268,11,(.group 6 91 false)⟩)
(.leaf ⟨58279,11,(.group 6 92 false)⟩)))
(.branch 58312
(.branch 58301
(.leaf ⟨58290,11,(.group 6 93 false)⟩)
(.leaf ⟨58301,11,(.group 6 94 false)⟩))
(.branch 58323
(.leaf ⟨58312,11,(.group 6 95 false)⟩)
(.leaf ⟨58323,11,(.group 6 96 false)⟩))))
(.branch 58378
(.branch 58356
(.branch 58345
(.leaf ⟨58334,11,(.group 6 97 false)⟩)
(.leaf ⟨58345,11,(.group 6 98 false)⟩))
(.branch 58367
(.leaf ⟨58356,11,(.group 6 99 false)⟩)
(.leaf ⟨58367,11,(.group 6 100 false)⟩)))
(.branch 58400
(.branch 58389
(.leaf ⟨58378,11,(.group 6 101 false)⟩)
(.leaf ⟨58389,11,(.group 6 102 false)⟩))
(.branch 58411
(.leaf ⟨58400,11,(.group 6 103 false)⟩)
(.leaf ⟨58411,11,(.group 6 104 false)⟩)))))
(.branch 58510
(.branch 58466
(.branch 58444
(.branch 58433
(.leaf ⟨58422,11,(.group 6 105 false)⟩)
(.leaf ⟨58433,11,(.group 6 106 false)⟩))
(.branch 58455
(.leaf ⟨58444,11,(.group 6 107 false)⟩)
(.leaf ⟨58455,11,(.group 6 108 false)⟩)))
(.branch 58488
(.branch 58477
(.leaf ⟨58466,11,(.group 6 109 false)⟩)
(.leaf ⟨58477,11,(.group 6 110 false)⟩))
(.branch 58499
(.leaf ⟨58488,11,(.group 6 111 false)⟩)
(.leaf ⟨58499,11,(.group 6 112 false)⟩))))
(.branch 58554
(.branch 58532
(.branch 58521
(.leaf ⟨58510,11,(.group 6 113 false)⟩)
(.leaf ⟨58521,11,(.group 7 31 false)⟩))
(.branch 58543
(.leaf ⟨58532,11,(.group 7 32 false)⟩)
(.leaf ⟨58543,11,(.group 7 33 false)⟩)))
(.branch 58576
(.branch 58565
(.leaf ⟨58554,11,(.group 7 34 false)⟩)
(.leaf ⟨58565,11,(.group 7 35 false)⟩))
(.branch 58587
(.leaf ⟨58576,11,(.group 7 36 false)⟩)
(.leaf ⟨58587,11,(.group 7 37 false)⟩)))))))

theorem tree56_checked : tree56.check 57894 58598 = true := by decide +kernel

def tree57 : Tree := (.branch 58950
(.branch 58774
(.branch 58686
(.branch 58642
(.branch 58620
(.branch 58609
(.leaf ⟨58598,11,(.group 7 38 false)⟩)
(.leaf ⟨58609,11,(.group 7 39 false)⟩))
(.branch 58631
(.leaf ⟨58620,11,(.group 7 40 false)⟩)
(.leaf ⟨58631,11,(.group 7 41 false)⟩)))
(.branch 58664
(.branch 58653
(.leaf ⟨58642,11,(.group 7 42 false)⟩)
(.leaf ⟨58653,11,(.group 7 43 false)⟩))
(.branch 58675
(.leaf ⟨58664,11,(.group 7 44 false)⟩)
(.leaf ⟨58675,11,(.group 7 45 false)⟩))))
(.branch 58730
(.branch 58708
(.branch 58697
(.leaf ⟨58686,11,(.group 7 46 false)⟩)
(.leaf ⟨58697,11,(.group 7 47 false)⟩))
(.branch 58719
(.leaf ⟨58708,11,(.group 7 48 false)⟩)
(.leaf ⟨58719,11,(.group 7 49 false)⟩)))
(.branch 58752
(.branch 58741
(.leaf ⟨58730,11,(.group 7 50 false)⟩)
(.leaf ⟨58741,11,(.group 7 51 false)⟩))
(.branch 58763
(.leaf ⟨58752,11,(.group 7 52 false)⟩)
(.leaf ⟨58763,11,(.group 7 53 false)⟩)))))
(.branch 58862
(.branch 58818
(.branch 58796
(.branch 58785
(.leaf ⟨58774,11,(.group 7 54 false)⟩)
(.leaf ⟨58785,11,(.group 7 55 false)⟩))
(.branch 58807
(.leaf ⟨58796,11,(.group 7 56 false)⟩)
(.leaf ⟨58807,11,(.group 7 57 false)⟩)))
(.branch 58840
(.branch 58829
(.leaf ⟨58818,11,(.group 7 58 false)⟩)
(.leaf ⟨58829,11,(.group 7 59 false)⟩))
(.branch 58851
(.leaf ⟨58840,11,(.group 7 60 false)⟩)
(.leaf ⟨58851,11,(.group 8 75 false)⟩))))
(.branch 58906
(.branch 58884
(.branch 58873
(.leaf ⟨58862,11,(.group 8 76 false)⟩)
(.leaf ⟨58873,11,(.group 8 77 false)⟩))
(.branch 58895
(.leaf ⟨58884,11,(.group 8 78 false)⟩)
(.leaf ⟨58895,11,(.group 8 79 false)⟩)))
(.branch 58928
(.branch 58917
(.leaf ⟨58906,11,(.group 8 80 false)⟩)
(.leaf ⟨58917,11,(.group 8 81 false)⟩))
(.branch 58939
(.leaf ⟨58928,11,(.group 8 82 false)⟩)
(.leaf ⟨58939,11,(.group 8 83 false)⟩))))))
(.branch 59126
(.branch 59038
(.branch 58994
(.branch 58972
(.branch 58961
(.leaf ⟨58950,11,(.group 8 84 false)⟩)
(.leaf ⟨58961,11,(.group 8 85 false)⟩))
(.branch 58983
(.leaf ⟨58972,11,(.group 8 86 false)⟩)
(.leaf ⟨58983,11,(.group 8 87 false)⟩)))
(.branch 59016
(.branch 59005
(.leaf ⟨58994,11,(.group 8 88 false)⟩)
(.leaf ⟨59005,11,(.group 8 89 false)⟩))
(.branch 59027
(.leaf ⟨59016,11,(.group 8 90 false)⟩)
(.leaf ⟨59027,11,(.group 8 91 false)⟩))))
(.branch 59082
(.branch 59060
(.branch 59049
(.leaf ⟨59038,11,(.group 8 92 false)⟩)
(.leaf ⟨59049,11,(.group 9 66 false)⟩))
(.branch 59071
(.leaf ⟨59060,11,(.group 9 67 false)⟩)
(.leaf ⟨59071,11,(.group 9 68 false)⟩)))
(.branch 59104
(.branch 59093
(.leaf ⟨59082,11,(.group 9 69 false)⟩)
(.leaf ⟨59093,11,(.group 9 70 false)⟩))
(.branch 59115
(.leaf ⟨59104,11,(.group 9 71 false)⟩)
(.leaf ⟨59115,11,(.group 9 72 false)⟩)))))
(.branch 59214
(.branch 59170
(.branch 59148
(.branch 59137
(.leaf ⟨59126,11,(.group 9 73 false)⟩)
(.leaf ⟨59137,11,(.group 9 74 false)⟩))
(.branch 59159
(.leaf ⟨59148,11,(.group 9 75 false)⟩)
(.leaf ⟨59159,11,(.group 9 76 false)⟩)))
(.branch 59192
(.branch 59181
(.leaf ⟨59170,11,(.group 9 77 false)⟩)
(.leaf ⟨59181,11,(.group 9 78 false)⟩))
(.branch 59203
(.leaf ⟨59192,11,(.group 9 79 false)⟩)
(.leaf ⟨59203,11,(.group 9 80 false)⟩))))
(.branch 59258
(.branch 59236
(.branch 59225
(.leaf ⟨59214,11,(.group 9 81 false)⟩)
(.leaf ⟨59225,11,(.group 9 82 false)⟩))
(.branch 59247
(.leaf ⟨59236,11,(.group 9 83 false)⟩)
(.leaf ⟨59247,11,(.group 9 84 false)⟩)))
(.branch 59280
(.branch 59269
(.leaf ⟨59258,11,(.group 9 85 false)⟩)
(.leaf ⟨59269,11,(.group 9 86 false)⟩))
(.branch 59291
(.leaf ⟨59280,11,(.group 9 87 false)⟩)
(.leaf ⟨59291,11,(.group 9 88 false)⟩)))))))

theorem tree57_checked : tree57.check 58598 59302 = true := by decide +kernel

def tree58 : Tree := (.branch 59683
(.branch 59491
(.branch 59395
(.branch 59347
(.branch 59324
(.branch 59313
(.leaf ⟨59302,11,(.group 10 49 false)⟩)
(.leaf ⟨59313,11,(.group 10 50 false)⟩))
(.branch 59335
(.leaf ⟨59324,11,(.group 10 51 false)⟩)
(.leaf ⟨59335,12,(.group 0 110 false)⟩)))
(.branch 59371
(.branch 59359
(.leaf ⟨59347,12,(.group 0 111 false)⟩)
(.leaf ⟨59359,12,(.group 0 112 false)⟩))
(.branch 59383
(.leaf ⟨59371,12,(.group 0 113 false)⟩)
(.leaf ⟨59383,12,(.group 0 114 false)⟩))))
(.branch 59443
(.branch 59419
(.branch 59407
(.leaf ⟨59395,12,(.group 0 115 false)⟩)
(.leaf ⟨59407,12,(.group 0 116 false)⟩))
(.branch 59431
(.leaf ⟨59419,12,(.group 0 117 false)⟩)
(.leaf ⟨59431,12,(.group 0 118 false)⟩)))
(.branch 59467
(.branch 59455
(.leaf ⟨59443,12,(.group 0 119 false)⟩)
(.leaf ⟨59455,12,(.group 0 120 false)⟩))
(.branch 59479
(.leaf ⟨59467,12,(.group 0 121 false)⟩)
(.leaf ⟨59479,12,(.group 0 122 false)⟩)))))
(.branch 59587
(.branch 59539
(.branch 59515
(.branch 59503
(.leaf ⟨59491,12,(.group 0 123 false)⟩)
(.leaf ⟨59503,12,(.group 0 124 false)⟩))
(.branch 59527
(.leaf ⟨59515,12,(.group 0 125 false)⟩)
(.leaf ⟨59527,12,(.group 0 126 false)⟩)))
(.branch 59563
(.branch 59551
(.leaf ⟨59539,12,(.group 0 127 false)⟩)
(.leaf ⟨59551,12,(.group 0 128 false)⟩))
(.branch 59575
(.leaf ⟨59563,12,(.group 0 129 false)⟩)
(.leaf ⟨59575,12,(.group 0 130 false)⟩))))
(.branch 59635
(.branch 59611
(.branch 59599
(.leaf ⟨59587,12,(.group 0 131 false)⟩)
(.leaf ⟨59599,12,(.group 0 132 false)⟩))
(.branch 59623
(.leaf ⟨59611,12,(.group 0 133 false)⟩)
(.leaf ⟨59623,12,(.group 0 134 false)⟩)))
(.branch 59659
(.branch 59647
(.leaf ⟨59635,12,(.group 0 135 false)⟩)
(.leaf ⟨59647,12,(.group 0 136 false)⟩))
(.branch 59671
(.leaf ⟨59659,12,(.group 0 137 false)⟩)
(.leaf ⟨59671,12,(.group 0 138 false)⟩))))))
(.branch 59875
(.branch 59779
(.branch 59731
(.branch 59707
(.branch 59695
(.leaf ⟨59683,12,(.group 0 139 false)⟩)
(.leaf ⟨59695,12,(.group 0 140 false)⟩))
(.branch 59719
(.leaf ⟨59707,12,(.group 0 141 false)⟩)
(.leaf ⟨59719,12,(.group 0 142 false)⟩)))
(.branch 59755
(.branch 59743
(.leaf ⟨59731,12,(.group 0 143 false)⟩)
(.leaf ⟨59743,12,(.group 0 144 false)⟩))
(.branch 59767
(.leaf ⟨59755,12,(.group 0 145 false)⟩)
(.leaf ⟨59767,12,(.group 0 146 false)⟩))))
(.branch 59827
(.branch 59803
(.branch 59791
(.leaf ⟨59779,12,(.group 0 147 false)⟩)
(.leaf ⟨59791,12,(.group 0 148 false)⟩))
(.branch 59815
(.leaf ⟨59803,12,(.group 0 149 false)⟩)
(.leaf ⟨59815,12,(.group 0 150 false)⟩)))
(.branch 59851
(.branch 59839
(.leaf ⟨59827,12,(.group 0 151 false)⟩)
(.leaf ⟨59839,12,(.group 0 152 false)⟩))
(.branch 59863
(.leaf ⟨59851,12,(.group 0 153 false)⟩)
(.leaf ⟨59863,12,(.group 0 154 false)⟩)))))
(.branch 59971
(.branch 59923
(.branch 59899
(.branch 59887
(.leaf ⟨59875,12,(.group 0 155 false)⟩)
(.leaf ⟨59887,12,(.group 0 156 false)⟩))
(.branch 59911
(.leaf ⟨59899,12,(.group 0 157 false)⟩)
(.leaf ⟨59911,12,(.group 0 158 false)⟩)))
(.branch 59947
(.branch 59935
(.leaf ⟨59923,12,(.group 0 159 false)⟩)
(.leaf ⟨59935,12,(.group 0 160 false)⟩))
(.branch 59959
(.leaf ⟨59947,12,(.group 0 161 false)⟩)
(.leaf ⟨59959,12,(.group 0 162 false)⟩))))
(.branch 60019
(.branch 59995
(.branch 59983
(.leaf ⟨59971,12,(.group 0 163 false)⟩)
(.leaf ⟨59983,12,(.group 0 164 false)⟩))
(.branch 60007
(.leaf ⟨59995,12,(.group 0 165 false)⟩)
(.leaf ⟨60007,12,(.group 1 35 false)⟩)))
(.branch 60043
(.branch 60031
(.leaf ⟨60019,12,(.group 1 36 false)⟩)
(.leaf ⟨60031,12,(.group 1 37 false)⟩))
(.branch 60055
(.leaf ⟨60043,12,(.group 1 38 false)⟩)
(.leaf ⟨60055,12,(.group 1 39 false)⟩)))))))

theorem tree58_checked : tree58.check 59302 60067 = true := by decide +kernel

def tree59 : Tree := (.branch 60451
(.branch 60259
(.branch 60163
(.branch 60115
(.branch 60091
(.branch 60079
(.leaf ⟨60067,12,(.group 1 40 false)⟩)
(.leaf ⟨60079,12,(.group 1 41 false)⟩))
(.branch 60103
(.leaf ⟨60091,12,(.group 1 42 false)⟩)
(.leaf ⟨60103,12,(.group 1 43 false)⟩)))
(.branch 60139
(.branch 60127
(.leaf ⟨60115,12,(.group 1 44 false)⟩)
(.leaf ⟨60127,12,(.group 1 45 false)⟩))
(.branch 60151
(.leaf ⟨60139,12,(.group 1 46 false)⟩)
(.leaf ⟨60151,12,(.group 1 47 false)⟩))))
(.branch 60211
(.branch 60187
(.branch 60175
(.leaf ⟨60163,12,(.group 1 48 false)⟩)
(.leaf ⟨60175,12,(.group 1 49 false)⟩))
(.branch 60199
(.leaf ⟨60187,12,(.group 1 50 false)⟩)
(.leaf ⟨60199,12,(.group 1 51 false)⟩)))
(.branch 60235
(.branch 60223
(.leaf ⟨60211,12,(.group 1 52 false)⟩)
(.leaf ⟨60223,12,(.group 1 53 false)⟩))
(.branch 60247
(.leaf ⟨60235,12,(.group 1 54 false)⟩)
(.leaf ⟨60247,12,(.group 1 55 false)⟩)))))
(.branch 60355
(.branch 60307
(.branch 60283
(.branch 60271
(.leaf ⟨60259,12,(.group 2 35 false)⟩)
(.leaf ⟨60271,12,(.group 2 36 false)⟩))
(.branch 60295
(.leaf ⟨60283,12,(.group 2 37 false)⟩)
(.leaf ⟨60295,12,(.group 2 38 false)⟩)))
(.branch 60331
(.branch 60319
(.leaf ⟨60307,12,(.group 2 39 false)⟩)
(.leaf ⟨60319,12,(.group 2 40 false)⟩))
(.branch 60343
(.leaf ⟨60331,12,(.group 2 41 false)⟩)
(.leaf ⟨60343,12,(.group 2 42 false)⟩))))
(.branch 60403
(.branch 60379
(.branch 60367
(.leaf ⟨60355,12,(.group 2 43 false)⟩)
(.leaf ⟨60367,12,(.group 2 44 false)⟩))
(.branch 60391
(.leaf ⟨60379,12,(.group 2 45 false)⟩)
(.leaf ⟨60391,12,(.group 2 46 false)⟩)))
(.branch 60427
(.branch 60415
(.leaf ⟨60403,12,(.group 2 47 false)⟩)
(.leaf ⟨60415,12,(.group 2 48 false)⟩))
(.branch 60439
(.leaf ⟨60427,12,(.group 2 49 false)⟩)
(.leaf ⟨60439,12,(.group 2 50 false)⟩))))))
(.branch 60643
(.branch 60547
(.branch 60499
(.branch 60475
(.branch 60463
(.leaf ⟨60451,12,(.group 2 51 false)⟩)
(.leaf ⟨60463,12,(.group 2 52 false)⟩))
(.branch 60487
(.leaf ⟨60475,12,(.group 2 53 false)⟩)
(.leaf ⟨60487,12,(.group 2 54 false)⟩)))
(.branch 60523
(.branch 60511
(.leaf ⟨60499,12,(.group 2 55 false)⟩)
(.leaf ⟨60511,12,(.group 3 35 false)⟩))
(.branch 60535
(.leaf ⟨60523,12,(.group 3 36 false)⟩)
(.leaf ⟨60535,12,(.group 3 37 false)⟩))))
(.branch 60595
(.branch 60571
(.branch 60559
(.leaf ⟨60547,12,(.group 3 38 false)⟩)
(.leaf ⟨60559,12,(.group 3 39 false)⟩))
(.branch 60583
(.leaf ⟨60571,12,(.group 3 40 false)⟩)
(.leaf ⟨60583,12,(.group 3 41 false)⟩)))
(.branch 60619
(.branch 60607
(.leaf ⟨60595,12,(.group 3 42 false)⟩)
(.leaf ⟨60607,12,(.group 3 43 false)⟩))
(.branch 60631
(.leaf ⟨60619,12,(.group 3 44 false)⟩)
(.leaf ⟨60631,12,(.group 3 45 false)⟩)))))
(.branch 60739
(.branch 60691
(.branch 60667
(.branch 60655
(.leaf ⟨60643,12,(.group 3 46 false)⟩)
(.leaf ⟨60655,12,(.group 3 47 false)⟩))
(.branch 60679
(.leaf ⟨60667,12,(.group 3 48 false)⟩)
(.leaf ⟨60679,12,(.group 3 49 false)⟩)))
(.branch 60715
(.branch 60703
(.leaf ⟨60691,12,(.group 3 50 false)⟩)
(.leaf ⟨60703,12,(.group 3 51 false)⟩))
(.branch 60727
(.leaf ⟨60715,12,(.group 3 52 false)⟩)
(.leaf ⟨60727,12,(.group 3 53 false)⟩))))
(.branch 60787
(.branch 60763
(.branch 60751
(.leaf ⟨60739,12,(.group 3 54 false)⟩)
(.leaf ⟨60751,12,(.group 3 55 false)⟩))
(.branch 60775
(.leaf ⟨60763,12,(.group 4 35 false)⟩)
(.leaf ⟨60775,12,(.group 4 36 false)⟩)))
(.branch 60811
(.branch 60799
(.leaf ⟨60787,12,(.group 4 37 false)⟩)
(.leaf ⟨60799,12,(.group 4 38 false)⟩))
(.branch 60823
(.leaf ⟨60811,12,(.group 4 39 false)⟩)
(.leaf ⟨60823,12,(.group 4 40 false)⟩)))))))

theorem tree59_checked : tree59.check 60067 60835 = true := by decide +kernel

def tree60 : Tree := (.branch 61219
(.branch 61027
(.branch 60931
(.branch 60883
(.branch 60859
(.branch 60847
(.leaf ⟨60835,12,(.group 4 41 false)⟩)
(.leaf ⟨60847,12,(.group 4 42 false)⟩))
(.branch 60871
(.leaf ⟨60859,12,(.group 4 43 false)⟩)
(.leaf ⟨60871,12,(.group 4 44 false)⟩)))
(.branch 60907
(.branch 60895
(.leaf ⟨60883,12,(.group 4 45 false)⟩)
(.leaf ⟨60895,12,(.group 4 46 false)⟩))
(.branch 60919
(.leaf ⟨60907,12,(.group 4 47 false)⟩)
(.leaf ⟨60919,12,(.group 4 48 false)⟩))))
(.branch 60979
(.branch 60955
(.branch 60943
(.leaf ⟨60931,12,(.group 4 49 false)⟩)
(.leaf ⟨60943,12,(.group 4 50 false)⟩))
(.branch 60967
(.leaf ⟨60955,12,(.group 4 51 false)⟩)
(.leaf ⟨60967,12,(.group 4 52 false)⟩)))
(.branch 61003
(.branch 60991
(.leaf ⟨60979,12,(.group 4 53 false)⟩)
(.leaf ⟨60991,12,(.group 4 54 false)⟩))
(.branch 61015
(.leaf ⟨61003,12,(.group 4 55 false)⟩)
(.leaf ⟨61015,12,(.group 5 622 false)⟩)))))
(.branch 61123
(.branch 61075
(.branch 61051
(.branch 61039
(.leaf ⟨61027,12,(.group 5 623 false)⟩)
(.leaf ⟨61039,12,(.group 5 624 false)⟩))
(.branch 61063
(.leaf ⟨61051,12,(.group 5 625 false)⟩)
(.leaf ⟨61063,12,(.group 5 626 false)⟩)))
(.branch 61099
(.branch 61087
(.leaf ⟨61075,12,(.group 5 627 false)⟩)
(.leaf ⟨61087,12,(.group 5 628 false)⟩))
(.branch 61111
(.leaf ⟨61099,12,(.group 5 629 false)⟩)
(.leaf ⟨61111,12,(.group 5 630 false)⟩))))
(.branch 61171
(.branch 61147
(.branch 61135
(.leaf ⟨61123,12,(.group 5 631 false)⟩)
(.leaf ⟨61135,12,(.group 5 632 false)⟩))
(.branch 61159
(.leaf ⟨61147,12,(.group 5 633 false)⟩)
(.leaf ⟨61159,12,(.group 5 634 false)⟩)))
(.branch 61195
(.branch 61183
(.leaf ⟨61171,12,(.group 5 635 false)⟩)
(.leaf ⟨61183,12,(.group 5 636 false)⟩))
(.branch 61207
(.leaf ⟨61195,12,(.group 5 637 false)⟩)
(.leaf ⟨61207,12,(.group 5 638 false)⟩))))))
(.branch 61411
(.branch 61315
(.branch 61267
(.branch 61243
(.branch 61231
(.leaf ⟨61219,12,(.group 5 639 false)⟩)
(.leaf ⟨61231,12,(.group 5 640 false)⟩))
(.branch 61255
(.leaf ⟨61243,12,(.group 5 641 false)⟩)
(.leaf ⟨61255,12,(.group 5 642 false)⟩)))
(.branch 61291
(.branch 61279
(.leaf ⟨61267,12,(.group 5 643 false)⟩)
(.leaf ⟨61279,12,(.group 5 644 false)⟩))
(.branch 61303
(.leaf ⟨61291,12,(.group 5 645 false)⟩)
(.leaf ⟨61303,12,(.group 5 646 false)⟩))))
(.branch 61363
(.branch 61339
(.branch 61327
(.leaf ⟨61315,12,(.group 5 647 false)⟩)
(.leaf ⟨61327,12,(.group 5 648 false)⟩))
(.branch 61351
(.leaf ⟨61339,12,(.group 5 649 false)⟩)
(.leaf ⟨61351,12,(.group 5 650 false)⟩)))
(.branch 61387
(.branch 61375
(.leaf ⟨61363,12,(.group 5 651 false)⟩)
(.leaf ⟨61375,12,(.group 5 652 false)⟩))
(.branch 61399
(.leaf ⟨61387,12,(.group 5 653 false)⟩)
(.leaf ⟨61399,12,(.group 5 654 false)⟩)))))
(.branch 61507
(.branch 61459
(.branch 61435
(.branch 61423
(.leaf ⟨61411,12,(.group 5 655 false)⟩)
(.leaf ⟨61423,12,(.group 5 656 false)⟩))
(.branch 61447
(.leaf ⟨61435,12,(.group 5 657 false)⟩)
(.leaf ⟨61447,12,(.group 5 658 false)⟩)))
(.branch 61483
(.branch 61471
(.leaf ⟨61459,12,(.group 5 659 false)⟩)
(.leaf ⟨61471,12,(.group 5 660 false)⟩))
(.branch 61495
(.leaf ⟨61483,12,(.group 5 661 false)⟩)
(.leaf ⟨61495,12,(.group 5 662 false)⟩))))
(.branch 61555
(.branch 61531
(.branch 61519
(.leaf ⟨61507,12,(.group 5 663 false)⟩)
(.leaf ⟨61519,12,(.group 5 664 false)⟩))
(.branch 61543
(.leaf ⟨61531,12,(.group 5 665 false)⟩)
(.leaf ⟨61543,12,(.group 5 666 false)⟩)))
(.branch 61579
(.branch 61567
(.leaf ⟨61555,12,(.group 5 667 false)⟩)
(.leaf ⟨61567,12,(.group 5 668 false)⟩))
(.branch 61591
(.leaf ⟨61579,12,(.group 5 669 false)⟩)
(.leaf ⟨61591,12,(.group 5 670 false)⟩)))))))

theorem tree60_checked : tree60.check 60835 61603 = true := by decide +kernel

def tree61 : Tree := (.branch 61987
(.branch 61795
(.branch 61699
(.branch 61651
(.branch 61627
(.branch 61615
(.leaf ⟨61603,12,(.group 5 671 false)⟩)
(.leaf ⟨61615,12,(.group 5 672 false)⟩))
(.branch 61639
(.leaf ⟨61627,12,(.group 5 673 false)⟩)
(.leaf ⟨61639,12,(.group 5 674 false)⟩)))
(.branch 61675
(.branch 61663
(.leaf ⟨61651,12,(.group 5 675 false)⟩)
(.leaf ⟨61663,12,(.group 5 676 false)⟩))
(.branch 61687
(.leaf ⟨61675,12,(.group 5 677 false)⟩)
(.leaf ⟨61687,12,(.group 5 678 false)⟩))))
(.branch 61747
(.branch 61723
(.branch 61711
(.leaf ⟨61699,12,(.group 5 679 false)⟩)
(.leaf ⟨61711,12,(.group 5 680 false)⟩))
(.branch 61735
(.leaf ⟨61723,12,(.group 5 681 false)⟩)
(.leaf ⟨61735,12,(.group 5 682 false)⟩)))
(.branch 61771
(.branch 61759
(.leaf ⟨61747,12,(.group 5 683 false)⟩)
(.leaf ⟨61759,12,(.group 5 684 false)⟩))
(.branch 61783
(.leaf ⟨61771,12,(.group 5 685 false)⟩)
(.leaf ⟨61783,12,(.group 5 686 false)⟩)))))
(.branch 61891
(.branch 61843
(.branch 61819
(.branch 61807
(.leaf ⟨61795,12,(.group 5 687 false)⟩)
(.leaf ⟨61807,12,(.group 5 688 false)⟩))
(.branch 61831
(.leaf ⟨61819,12,(.group 5 689 false)⟩)
(.leaf ⟨61831,12,(.group 5 690 false)⟩)))
(.branch 61867
(.branch 61855
(.leaf ⟨61843,12,(.group 5 691 false)⟩)
(.leaf ⟨61855,12,(.group 5 692 false)⟩))
(.branch 61879
(.leaf ⟨61867,12,(.group 5 693 false)⟩)
(.leaf ⟨61879,12,(.group 5 694 false)⟩))))
(.branch 61939
(.branch 61915
(.branch 61903
(.leaf ⟨61891,12,(.group 5 695 false)⟩)
(.leaf ⟨61903,12,(.group 5 696 false)⟩))
(.branch 61927
(.leaf ⟨61915,12,(.group 5 697 false)⟩)
(.leaf ⟨61927,12,(.group 5 698 false)⟩)))
(.branch 61963
(.branch 61951
(.leaf ⟨61939,12,(.group 5 699 false)⟩)
(.leaf ⟨61951,12,(.group 5 700 false)⟩))
(.branch 61975
(.leaf ⟨61963,12,(.group 5 701 false)⟩)
(.leaf ⟨61975,12,(.group 5 702 false)⟩))))))
(.branch 62179
(.branch 62083
(.branch 62035
(.branch 62011
(.branch 61999
(.leaf ⟨61987,12,(.group 5 703 false)⟩)
(.leaf ⟨61999,12,(.group 5 704 false)⟩))
(.branch 62023
(.leaf ⟨62011,12,(.group 5 705 false)⟩)
(.leaf ⟨62023,12,(.group 5 706 false)⟩)))
(.branch 62059
(.branch 62047
(.leaf ⟨62035,12,(.group 5 707 false)⟩)
(.leaf ⟨62047,12,(.group 5 708 false)⟩))
(.branch 62071
(.leaf ⟨62059,12,(.group 5 709 false)⟩)
(.leaf ⟨62071,12,(.group 6 114 false)⟩))))
(.branch 62131
(.branch 62107
(.branch 62095
(.leaf ⟨62083,12,(.group 6 115 false)⟩)
(.leaf ⟨62095,12,(.group 6 116 false)⟩))
(.branch 62119
(.leaf ⟨62107,12,(.group 6 117 false)⟩)
(.leaf ⟨62119,12,(.group 6 118 false)⟩)))
(.branch 62155
(.branch 62143
(.leaf ⟨62131,12,(.group 6 119 false)⟩)
(.leaf ⟨62143,12,(.group 6 120 false)⟩))
(.branch 62167
(.leaf ⟨62155,12,(.group 6 121 false)⟩)
(.leaf ⟨62167,12,(.group 6 122 false)⟩)))))
(.branch 62275
(.branch 62227
(.branch 62203
(.branch 62191
(.leaf ⟨62179,12,(.group 6 123 false)⟩)
(.leaf ⟨62191,12,(.group 6 124 false)⟩))
(.branch 62215
(.leaf ⟨62203,12,(.group 6 125 false)⟩)
(.leaf ⟨62215,12,(.group 6 126 false)⟩)))
(.branch 62251
(.branch 62239
(.leaf ⟨62227,12,(.group 6 127 false)⟩)
(.leaf ⟨62239,12,(.group 6 128 false)⟩))
(.branch 62263
(.leaf ⟨62251,12,(.group 6 129 false)⟩)
(.leaf ⟨62263,12,(.group 6 130 false)⟩))))
(.branch 62323
(.branch 62299
(.branch 62287
(.leaf ⟨62275,12,(.group 6 131 false)⟩)
(.leaf ⟨62287,12,(.group 6 132 false)⟩))
(.branch 62311
(.leaf ⟨62299,12,(.group 6 133 false)⟩)
(.leaf ⟨62311,12,(.group 6 134 false)⟩)))
(.branch 62347
(.branch 62335
(.leaf ⟨62323,12,(.group 6 135 false)⟩)
(.leaf ⟨62335,12,(.group 6 136 false)⟩))
(.branch 62359
(.leaf ⟨62347,12,(.group 6 137 false)⟩)
(.leaf ⟨62359,12,(.group 6 138 false)⟩)))))))

theorem tree61_checked : tree61.check 61603 62371 = true := by decide +kernel

def tree62 : Tree := (.branch 62755
(.branch 62563
(.branch 62467
(.branch 62419
(.branch 62395
(.branch 62383
(.leaf ⟨62371,12,(.group 6 139 false)⟩)
(.leaf ⟨62383,12,(.group 6 140 false)⟩))
(.branch 62407
(.leaf ⟨62395,12,(.group 6 141 false)⟩)
(.leaf ⟨62407,12,(.group 6 142 false)⟩)))
(.branch 62443
(.branch 62431
(.leaf ⟨62419,12,(.group 6 143 false)⟩)
(.leaf ⟨62431,12,(.group 6 144 false)⟩))
(.branch 62455
(.leaf ⟨62443,12,(.group 6 145 false)⟩)
(.leaf ⟨62455,12,(.group 6 146 false)⟩))))
(.branch 62515
(.branch 62491
(.branch 62479
(.leaf ⟨62467,12,(.group 6 147 false)⟩)
(.leaf ⟨62479,12,(.group 6 148 false)⟩))
(.branch 62503
(.leaf ⟨62491,12,(.group 6 149 false)⟩)
(.leaf ⟨62503,12,(.group 6 150 false)⟩)))
(.branch 62539
(.branch 62527
(.leaf ⟨62515,12,(.group 6 151 false)⟩)
(.leaf ⟨62527,12,(.group 6 152 false)⟩))
(.branch 62551
(.leaf ⟨62539,12,(.group 6 153 false)⟩)
(.leaf ⟨62551,12,(.group 6 154 false)⟩)))))
(.branch 62659
(.branch 62611
(.branch 62587
(.branch 62575
(.leaf ⟨62563,12,(.group 6 155 false)⟩)
(.leaf ⟨62575,12,(.group 6 156 false)⟩))
(.branch 62599
(.leaf ⟨62587,12,(.group 6 157 false)⟩)
(.leaf ⟨62599,12,(.group 6 158 false)⟩)))
(.branch 62635
(.branch 62623
(.leaf ⟨62611,12,(.group 6 159 false)⟩)
(.leaf ⟨62623,12,(.group 6 160 false)⟩))
(.branch 62647
(.leaf ⟨62635,12,(.group 6 161 false)⟩)
(.leaf ⟨62647,12,(.group 6 162 false)⟩))))
(.branch 62707
(.branch 62683
(.branch 62671
(.leaf ⟨62659,12,(.group 6 163 false)⟩)
(.leaf ⟨62671,12,(.group 6 164 false)⟩))
(.branch 62695
(.leaf ⟨62683,12,(.group 6 165 false)⟩)
(.leaf ⟨62695,12,(.group 6 166 false)⟩)))
(.branch 62731
(.branch 62719
(.leaf ⟨62707,12,(.group 6 167 false)⟩)
(.leaf ⟨62719,12,(.group 6 168 false)⟩))
(.branch 62743
(.leaf ⟨62731,12,(.group 6 169 false)⟩)
(.leaf ⟨62743,12,(.group 6 170 false)⟩))))))
(.branch 62947
(.branch 62851
(.branch 62803
(.branch 62779
(.branch 62767
(.leaf ⟨62755,12,(.group 6 171 false)⟩)
(.leaf ⟨62767,12,(.group 6 172 false)⟩))
(.branch 62791
(.leaf ⟨62779,12,(.group 6 173 false)⟩)
(.leaf ⟨62791,12,(.group 6 174 false)⟩)))
(.branch 62827
(.branch 62815
(.leaf ⟨62803,12,(.group 6 175 false)⟩)
(.leaf ⟨62815,12,(.group 6 176 false)⟩))
(.branch 62839
(.leaf ⟨62827,12,(.group 6 177 false)⟩)
(.leaf ⟨62839,12,(.group 6 178 false)⟩))))
(.branch 62899
(.branch 62875
(.branch 62863
(.leaf ⟨62851,12,(.group 6 179 false)⟩)
(.leaf ⟨62863,12,(.group 6 180 false)⟩))
(.branch 62887
(.leaf ⟨62875,12,(.group 6 181 false)⟩)
(.leaf ⟨62887,12,(.group 6 182 false)⟩)))
(.branch 62923
(.branch 62911
(.leaf ⟨62899,12,(.group 6 183 false)⟩)
(.leaf ⟨62911,12,(.group 6 184 false)⟩))
(.branch 62935
(.leaf ⟨62923,12,(.group 6 185 false)⟩)
(.leaf ⟨62935,12,(.group 6 186 false)⟩)))))
(.branch 63043
(.branch 62995
(.branch 62971
(.branch 62959
(.leaf ⟨62947,12,(.group 6 187 false)⟩)
(.leaf ⟨62959,12,(.group 6 188 false)⟩))
(.branch 62983
(.leaf ⟨62971,12,(.group 6 189 false)⟩)
(.leaf ⟨62983,12,(.group 6 190 false)⟩)))
(.branch 63019
(.branch 63007
(.leaf ⟨62995,12,(.group 7 61 false)⟩)
(.leaf ⟨63007,12,(.group 7 62 false)⟩))
(.branch 63031
(.leaf ⟨63019,12,(.group 7 63 false)⟩)
(.leaf ⟨63031,12,(.group 7 64 false)⟩))))
(.branch 63091
(.branch 63067
(.branch 63055
(.leaf ⟨63043,12,(.group 7 65 false)⟩)
(.leaf ⟨63055,12,(.group 7 66 false)⟩))
(.branch 63079
(.leaf ⟨63067,12,(.group 7 67 false)⟩)
(.leaf ⟨63079,12,(.group 7 68 false)⟩)))
(.branch 63115
(.branch 63103
(.leaf ⟨63091,12,(.group 7 69 false)⟩)
(.leaf ⟨63103,12,(.group 7 70 false)⟩))
(.branch 63127
(.leaf ⟨63115,12,(.group 7 71 false)⟩)
(.leaf ⟨63127,12,(.group 7 72 false)⟩)))))))

theorem tree62_checked : tree62.check 62371 63139 = true := by decide +kernel

def tree63 : Tree := (.branch 63523
(.branch 63331
(.branch 63235
(.branch 63187
(.branch 63163
(.branch 63151
(.leaf ⟨63139,12,(.group 7 73 false)⟩)
(.leaf ⟨63151,12,(.group 7 74 false)⟩))
(.branch 63175
(.leaf ⟨63163,12,(.group 7 75 false)⟩)
(.leaf ⟨63175,12,(.group 7 76 false)⟩)))
(.branch 63211
(.branch 63199
(.leaf ⟨63187,12,(.group 7 77 false)⟩)
(.leaf ⟨63199,12,(.group 7 78 false)⟩))
(.branch 63223
(.leaf ⟨63211,12,(.group 7 79 false)⟩)
(.leaf ⟨63223,12,(.group 7 80 false)⟩))))
(.branch 63283
(.branch 63259
(.branch 63247
(.leaf ⟨63235,12,(.group 7 81 false)⟩)
(.leaf ⟨63247,12,(.group 8 96 false)⟩))
(.branch 63271
(.leaf ⟨63259,12,(.group 8 97 false)⟩)
(.leaf ⟨63271,12,(.group 8 98 false)⟩)))
(.branch 63307
(.branch 63295
(.leaf ⟨63283,12,(.group 8 99 false)⟩)
(.leaf ⟨63295,12,(.group 8 100 false)⟩))
(.branch 63319
(.leaf ⟨63307,12,(.group 8 101 false)⟩)
(.leaf ⟨63319,12,(.group 8 102 false)⟩)))))
(.branch 63427
(.branch 63379
(.branch 63355
(.branch 63343
(.leaf ⟨63331,12,(.group 8 103 false)⟩)
(.leaf ⟨63343,12,(.group 8 104 false)⟩))
(.branch 63367
(.leaf ⟨63355,12,(.group 8 105 false)⟩)
(.leaf ⟨63367,12,(.group 8 106 false)⟩)))
(.branch 63403
(.branch 63391
(.leaf ⟨63379,12,(.group 8 107 false)⟩)
(.leaf ⟨63391,12,(.group 8 108 false)⟩))
(.branch 63415
(.leaf ⟨63403,12,(.group 8 109 false)⟩)
(.leaf ⟨63415,12,(.group 8 110 false)⟩))))
(.branch 63475
(.branch 63451
(.branch 63439
(.leaf ⟨63427,12,(.group 8 111 false)⟩)
(.leaf ⟨63439,12,(.group 8 112 false)⟩))
(.branch 63463
(.leaf ⟨63451,12,(.group 8 113 false)⟩)
(.leaf ⟨63463,12,(.group 8 114 false)⟩)))
(.branch 63499
(.branch 63487
(.leaf ⟨63475,12,(.group 8 115 false)⟩)
(.leaf ⟨63487,12,(.group 8 116 false)⟩))
(.branch 63511
(.leaf ⟨63499,12,(.group 8 117 false)⟩)
(.leaf ⟨63511,12,(.group 8 118 false)⟩))))))
(.branch 63715
(.branch 63619
(.branch 63571
(.branch 63547
(.branch 63535
(.leaf ⟨63523,12,(.group 8 119 false)⟩)
(.leaf ⟨63535,12,(.group 8 120 false)⟩))
(.branch 63559
(.leaf ⟨63547,12,(.group 9 92 false)⟩)
(.leaf ⟨63559,12,(.group 9 93 false)⟩)))
(.branch 63595
(.branch 63583
(.leaf ⟨63571,12,(.group 9 94 false)⟩)
(.leaf ⟨63583,12,(.group 9 95 false)⟩))
(.branch 63607
(.leaf ⟨63595,12,(.group 9 96 false)⟩)
(.leaf ⟨63607,12,(.group 9 97 false)⟩))))
(.branch 63667
(.branch 63643
(.branch 63631
(.leaf ⟨63619,12,(.group 9 98 false)⟩)
(.leaf ⟨63631,12,(.group 9 99 false)⟩))
(.branch 63655
(.leaf ⟨63643,12,(.group 9 100 false)⟩)
(.leaf ⟨63655,12,(.group 9 101 false)⟩)))
(.branch 63691
(.branch 63679
(.leaf ⟨63667,12,(.group 9 102 false)⟩)
(.leaf ⟨63679,12,(.group 9 103 false)⟩))
(.branch 63703
(.leaf ⟨63691,12,(.group 9 104 false)⟩)
(.leaf ⟨63703,12,(.group 9 105 false)⟩)))))
(.branch 63811
(.branch 63763
(.branch 63739
(.branch 63727
(.leaf ⟨63715,12,(.group 9 106 false)⟩)
(.leaf ⟨63727,12,(.group 9 107 false)⟩))
(.branch 63751
(.leaf ⟨63739,12,(.group 9 108 false)⟩)
(.leaf ⟨63751,12,(.group 9 109 false)⟩)))
(.branch 63787
(.branch 63775
(.leaf ⟨63763,12,(.group 9 110 false)⟩)
(.leaf ⟨63775,12,(.group 9 111 false)⟩))
(.branch 63799
(.leaf ⟨63787,12,(.group 9 112 false)⟩)
(.leaf ⟨63799,12,(.group 9 113 false)⟩))))
(.branch 63859
(.branch 63835
(.branch 63823
(.leaf ⟨63811,12,(.group 9 114 false)⟩)
(.leaf ⟨63823,12,(.group 9 115 false)⟩))
(.branch 63847
(.leaf ⟨63835,12,(.group 9 116 false)⟩)
(.leaf ⟨63847,12,(.group 10 64 false)⟩)))
(.branch 63883
(.branch 63871
(.leaf ⟨63859,12,(.group 10 65 false)⟩)
(.leaf ⟨63871,12,(.group 10 66 false)⟩))
(.branch 63895
(.leaf ⟨63883,12,(.group 10 67 false)⟩)
(.leaf ⟨63895,12,(.group 10 68 false)⟩)))))))

theorem tree63_checked : tree63.check 63139 63907 = true := by decide +kernel

def tree64 : Tree := (.branch 64313
(.branch 64105
(.branch 64003
(.branch 63955
(.branch 63931
(.branch 63919
(.leaf ⟨63907,12,(.group 10 69 false)⟩)
(.leaf ⟨63919,12,(.group 10 70 false)⟩))
(.branch 63943
(.leaf ⟨63931,12,(.group 10 71 false)⟩)
(.leaf ⟨63943,12,(.group 10 72 false)⟩)))
(.branch 63979
(.branch 63967
(.leaf ⟨63955,12,(.group 10 73 false)⟩)
(.leaf ⟨63967,12,(.group 10 74 false)⟩))
(.branch 63991
(.leaf ⟨63979,12,(.group 10 75 false)⟩)
(.leaf ⟨63991,12,(.group 10 76 false)⟩))))
(.branch 64053
(.branch 64027
(.branch 64015
(.leaf ⟨64003,12,(.group 10 77 false)⟩)
(.leaf ⟨64015,12,(.group 10 78 false)⟩))
(.branch 64040
(.leaf ⟨64027,13,(.group 0 166 false)⟩)
(.leaf ⟨64040,13,(.group 0 167 false)⟩)))
(.branch 64079
(.branch 64066
(.leaf ⟨64053,13,(.group 0 168 false)⟩)
(.leaf ⟨64066,13,(.group 0 169 false)⟩))
(.branch 64092
(.leaf ⟨64079,13,(.group 0 170 false)⟩)
(.leaf ⟨64092,13,(.group 0 171 false)⟩)))))
(.branch 64209
(.branch 64157
(.branch 64131
(.branch 64118
(.leaf ⟨64105,13,(.group 0 172 false)⟩)
(.leaf ⟨64118,13,(.group 0 173 false)⟩))
(.branch 64144
(.leaf ⟨64131,13,(.group 0 174 false)⟩)
(.leaf ⟨64144,13,(.group 0 175 false)⟩)))
(.branch 64183
(.branch 64170
(.leaf ⟨64157,13,(.group 0 176 false)⟩)
(.leaf ⟨64170,13,(.group 0 177 false)⟩))
(.branch 64196
(.leaf ⟨64183,13,(.group 0 178 false)⟩)
(.leaf ⟨64196,13,(.group 0 179 false)⟩))))
(.branch 64261
(.branch 64235
(.branch 64222
(.leaf ⟨64209,13,(.group 0 180 false)⟩)
(.leaf ⟨64222,13,(.group 0 181 false)⟩))
(.branch 64248
(.leaf ⟨64235,13,(.group 0 182 false)⟩)
(.leaf ⟨64248,13,(.group 0 183 false)⟩)))
(.branch 64287
(.branch 64274
(.leaf ⟨64261,13,(.group 0 184 false)⟩)
(.leaf ⟨64274,13,(.group 0 185 false)⟩))
(.branch 64300
(.leaf ⟨64287,13,(.group 0 186 false)⟩)
(.leaf ⟨64300,13,(.group 0 187 false)⟩))))))
(.branch 64521
(.branch 64417
(.branch 64365
(.branch 64339
(.branch 64326
(.leaf ⟨64313,13,(.group 0 188 false)⟩)
(.leaf ⟨64326,13,(.group 0 189 false)⟩))
(.branch 64352
(.leaf ⟨64339,13,(.group 0 190 false)⟩)
(.leaf ⟨64352,13,(.group 0 191 false)⟩)))
(.branch 64391
(.branch 64378
(.leaf ⟨64365,13,(.group 0 192 false)⟩)
(.leaf ⟨64378,13,(.group 0 193 false)⟩))
(.branch 64404
(.leaf ⟨64391,13,(.group 0 194 false)⟩)
(.leaf ⟨64404,13,(.group 0 195 false)⟩))))
(.branch 64469
(.branch 64443
(.branch 64430
(.leaf ⟨64417,13,(.group 0 196 false)⟩)
(.leaf ⟨64430,13,(.group 0 197 false)⟩))
(.branch 64456
(.leaf ⟨64443,13,(.group 0 198 false)⟩)
(.leaf ⟨64456,13,(.group 0 199 false)⟩)))
(.branch 64495
(.branch 64482
(.leaf ⟨64469,13,(.group 0 200 false)⟩)
(.leaf ⟨64482,13,(.group 0 201 false)⟩))
(.branch 64508
(.leaf ⟨64495,13,(.group 0 202 false)⟩)
(.leaf ⟨64508,13,(.group 0 203 false)⟩)))))
(.branch 64625
(.branch 64573
(.branch 64547
(.branch 64534
(.leaf ⟨64521,13,(.group 0 204 false)⟩)
(.leaf ⟨64534,13,(.group 0 205 false)⟩))
(.branch 64560
(.leaf ⟨64547,13,(.group 0 206 false)⟩)
(.leaf ⟨64560,13,(.group 0 207 false)⟩)))
(.branch 64599
(.branch 64586
(.leaf ⟨64573,13,(.group 0 208 false)⟩)
(.leaf ⟨64586,13,(.group 0 209 false)⟩))
(.branch 64612
(.leaf ⟨64599,13,(.group 0 210 false)⟩)
(.leaf ⟨64612,13,(.group 0 211 false)⟩))))
(.branch 64677
(.branch 64651
(.branch 64638
(.leaf ⟨64625,13,(.group 0 212 false)⟩)
(.leaf ⟨64638,13,(.group 0 213 false)⟩))
(.branch 64664
(.leaf ⟨64651,13,(.group 0 214 false)⟩)
(.leaf ⟨64664,13,(.group 0 215 false)⟩)))
(.branch 64703
(.branch 64690
(.leaf ⟨64677,13,(.group 0 216 false)⟩)
(.leaf ⟨64690,13,(.group 0 217 false)⟩))
(.branch 64716
(.leaf ⟨64703,13,(.group 0 218 false)⟩)
(.leaf ⟨64716,13,(.group 0 219 false)⟩)))))))

theorem tree64_checked : tree64.check 63907 64729 = true := by decide +kernel

def tree65 : Tree := (.branch 65145
(.branch 64937
(.branch 64833
(.branch 64781
(.branch 64755
(.branch 64742
(.leaf ⟨64729,13,(.group 0 220 false)⟩)
(.leaf ⟨64742,13,(.group 0 221 false)⟩))
(.branch 64768
(.leaf ⟨64755,13,(.group 0 222 false)⟩)
(.leaf ⟨64768,13,(.group 0 223 false)⟩)))
(.branch 64807
(.branch 64794
(.leaf ⟨64781,13,(.group 0 224 false)⟩)
(.leaf ⟨64794,13,(.group 0 225 false)⟩))
(.branch 64820
(.leaf ⟨64807,13,(.group 0 226 false)⟩)
(.leaf ⟨64820,13,(.group 0 227 false)⟩))))
(.branch 64885
(.branch 64859
(.branch 64846
(.leaf ⟨64833,13,(.group 0 228 false)⟩)
(.leaf ⟨64846,13,(.group 0 229 false)⟩))
(.branch 64872
(.leaf ⟨64859,13,(.group 0 230 false)⟩)
(.leaf ⟨64872,13,(.group 0 231 false)⟩)))
(.branch 64911
(.branch 64898
(.leaf ⟨64885,13,(.group 0 232 false)⟩)
(.leaf ⟨64898,13,(.group 0 233 false)⟩))
(.branch 64924
(.leaf ⟨64911,13,(.group 0 234 false)⟩)
(.leaf ⟨64924,13,(.group 0 235 false)⟩)))))
(.branch 65041
(.branch 64989
(.branch 64963
(.branch 64950
(.leaf ⟨64937,13,(.group 0 236 false)⟩)
(.leaf ⟨64950,13,(.group 0 237 false)⟩))
(.branch 64976
(.leaf ⟨64963,13,(.group 1 56 false)⟩)
(.leaf ⟨64976,13,(.group 1 57 false)⟩)))
(.branch 65015
(.branch 65002
(.leaf ⟨64989,13,(.group 1 58 false)⟩)
(.leaf ⟨65002,13,(.group 1 59 false)⟩))
(.branch 65028
(.leaf ⟨65015,13,(.group 1 60 false)⟩)
(.leaf ⟨65028,13,(.group 1 61 false)⟩))))
(.branch 65093
(.branch 65067
(.branch 65054
(.leaf ⟨65041,13,(.group 1 62 false)⟩)
(.leaf ⟨65054,13,(.group 1 63 false)⟩))
(.branch 65080
(.leaf ⟨65067,13,(.group 1 64 false)⟩)
(.leaf ⟨65080,13,(.group 1 65 false)⟩)))
(.branch 65119
(.branch 65106
(.leaf ⟨65093,13,(.group 1 66 false)⟩)
(.leaf ⟨65106,13,(.group 1 67 false)⟩))
(.branch 65132
(.leaf ⟨65119,13,(.group 1 68 false)⟩)
(.leaf ⟨65132,13,(.group 1 69 false)⟩))))))
(.branch 65353
(.branch 65249
(.branch 65197
(.branch 65171
(.branch 65158
(.leaf ⟨65145,13,(.group 1 70 false)⟩)
(.leaf ⟨65158,13,(.group 1 71 false)⟩))
(.branch 65184
(.leaf ⟨65171,13,(.group 1 72 false)⟩)
(.leaf ⟨65184,13,(.group 1 73 false)⟩)))
(.branch 65223
(.branch 65210
(.leaf ⟨65197,13,(.group 1 74 false)⟩)
(.leaf ⟨65210,13,(.group 1 75 false)⟩))
(.branch 65236
(.leaf ⟨65223,13,(.group 1 76 false)⟩)
(.leaf ⟨65236,13,(.group 1 77 false)⟩))))
(.branch 65301
(.branch 65275
(.branch 65262
(.leaf ⟨65249,13,(.group 1 78 false)⟩)
(.leaf ⟨65262,13,(.group 1 79 false)⟩))
(.branch 65288
(.leaf ⟨65275,13,(.group 1 80 false)⟩)
(.leaf ⟨65288,13,(.group 1 81 false)⟩)))
(.branch 65327
(.branch 65314
(.leaf ⟨65301,13,(.group 1 82 false)⟩)
(.leaf ⟨65314,13,(.group 1 83 false)⟩))
(.branch 65340
(.leaf ⟨65327,13,(.group 2 56 false)⟩)
(.leaf ⟨65340,13,(.group 2 57 false)⟩)))))
(.branch 65457
(.branch 65405
(.branch 65379
(.branch 65366
(.leaf ⟨65353,13,(.group 2 58 false)⟩)
(.leaf ⟨65366,13,(.group 2 59 false)⟩))
(.branch 65392
(.leaf ⟨65379,13,(.group 2 60 false)⟩)
(.leaf ⟨65392,13,(.group 2 61 false)⟩)))
(.branch 65431
(.branch 65418
(.leaf ⟨65405,13,(.group 2 62 false)⟩)
(.leaf ⟨65418,13,(.group 2 63 false)⟩))
(.branch 65444
(.leaf ⟨65431,13,(.group 2 64 false)⟩)
(.leaf ⟨65444,13,(.group 2 65 false)⟩))))
(.branch 65509
(.branch 65483
(.branch 65470
(.leaf ⟨65457,13,(.group 2 66 false)⟩)
(.leaf ⟨65470,13,(.group 2 67 false)⟩))
(.branch 65496
(.leaf ⟨65483,13,(.group 2 68 false)⟩)
(.leaf ⟨65496,13,(.group 2 69 false)⟩)))
(.branch 65535
(.branch 65522
(.leaf ⟨65509,13,(.group 2 70 false)⟩)
(.leaf ⟨65522,13,(.group 2 71 false)⟩))
(.branch 65548
(.leaf ⟨65535,13,(.group 2 72 false)⟩)
(.leaf ⟨65548,13,(.group 2 73 false)⟩)))))))

theorem tree65_checked : tree65.check 64729 65561 = true := by decide +kernel

def tree66 : Tree := (.branch 65977
(.branch 65769
(.branch 65665
(.branch 65613
(.branch 65587
(.branch 65574
(.leaf ⟨65561,13,(.group 2 74 false)⟩)
(.leaf ⟨65574,13,(.group 2 75 false)⟩))
(.branch 65600
(.leaf ⟨65587,13,(.group 2 76 false)⟩)
(.leaf ⟨65600,13,(.group 2 77 false)⟩)))
(.branch 65639
(.branch 65626
(.leaf ⟨65613,13,(.group 2 78 false)⟩)
(.leaf ⟨65626,13,(.group 2 79 false)⟩))
(.branch 65652
(.leaf ⟨65639,13,(.group 2 80 false)⟩)
(.leaf ⟨65652,13,(.group 2 81 false)⟩))))
(.branch 65717
(.branch 65691
(.branch 65678
(.leaf ⟨65665,13,(.group 2 82 false)⟩)
(.leaf ⟨65678,13,(.group 2 83 false)⟩))
(.branch 65704
(.leaf ⟨65691,13,(.group 3 56 false)⟩)
(.leaf ⟨65704,13,(.group 3 57 false)⟩)))
(.branch 65743
(.branch 65730
(.leaf ⟨65717,13,(.group 3 58 false)⟩)
(.leaf ⟨65730,13,(.group 3 59 false)⟩))
(.branch 65756
(.leaf ⟨65743,13,(.group 3 60 false)⟩)
(.leaf ⟨65756,13,(.group 3 61 false)⟩)))))
(.branch 65873
(.branch 65821
(.branch 65795
(.branch 65782
(.leaf ⟨65769,13,(.group 3 62 false)⟩)
(.leaf ⟨65782,13,(.group 3 63 false)⟩))
(.branch 65808
(.leaf ⟨65795,13,(.group 3 64 false)⟩)
(.leaf ⟨65808,13,(.group 3 65 false)⟩)))
(.branch 65847
(.branch 65834
(.leaf ⟨65821,13,(.group 3 66 false)⟩)
(.leaf ⟨65834,13,(.group 3 67 false)⟩))
(.branch 65860
(.leaf ⟨65847,13,(.group 3 68 false)⟩)
(.leaf ⟨65860,13,(.group 3 69 false)⟩))))
(.branch 65925
(.branch 65899
(.branch 65886
(.leaf ⟨65873,13,(.group 3 70 false)⟩)
(.leaf ⟨65886,13,(.group 3 71 false)⟩))
(.branch 65912
(.leaf ⟨65899,13,(.group 3 72 false)⟩)
(.leaf ⟨65912,13,(.group 3 73 false)⟩)))
(.branch 65951
(.branch 65938
(.leaf ⟨65925,13,(.group 3 74 false)⟩)
(.leaf ⟨65938,13,(.group 3 75 false)⟩))
(.branch 65964
(.leaf ⟨65951,13,(.group 3 76 false)⟩)
(.leaf ⟨65964,13,(.group 3 77 false)⟩))))))
(.branch 66185
(.branch 66081
(.branch 66029
(.branch 66003
(.branch 65990
(.leaf ⟨65977,13,(.group 3 78 false)⟩)
(.leaf ⟨65990,13,(.group 3 79 false)⟩))
(.branch 66016
(.leaf ⟨66003,13,(.group 3 80 false)⟩)
(.leaf ⟨66016,13,(.group 3 81 false)⟩)))
(.branch 66055
(.branch 66042
(.leaf ⟨66029,13,(.group 3 82 false)⟩)
(.leaf ⟨66042,13,(.group 3 83 false)⟩))
(.branch 66068
(.leaf ⟨66055,13,(.group 4 56 false)⟩)
(.leaf ⟨66068,13,(.group 4 57 false)⟩))))
(.branch 66133
(.branch 66107
(.branch 66094
(.leaf ⟨66081,13,(.group 4 58 false)⟩)
(.leaf ⟨66094,13,(.group 4 59 false)⟩))
(.branch 66120
(.leaf ⟨66107,13,(.group 4 60 false)⟩)
(.leaf ⟨66120,13,(.group 4 61 false)⟩)))
(.branch 66159
(.branch 66146
(.leaf ⟨66133,13,(.group 4 62 false)⟩)
(.leaf ⟨66146,13,(.group 4 63 false)⟩))
(.branch 66172
(.leaf ⟨66159,13,(.group 4 64 false)⟩)
(.leaf ⟨66172,13,(.group 4 65 false)⟩)))))
(.branch 66289
(.branch 66237
(.branch 66211
(.branch 66198
(.leaf ⟨66185,13,(.group 4 66 false)⟩)
(.leaf ⟨66198,13,(.group 4 67 false)⟩))
(.branch 66224
(.leaf ⟨66211,13,(.group 4 68 false)⟩)
(.leaf ⟨66224,13,(.group 4 69 false)⟩)))
(.branch 66263
(.branch 66250
(.leaf ⟨66237,13,(.group 4 70 false)⟩)
(.leaf ⟨66250,13,(.group 4 71 false)⟩))
(.branch 66276
(.leaf ⟨66263,13,(.group 4 72 false)⟩)
(.leaf ⟨66276,13,(.group 4 73 false)⟩))))
(.branch 66341
(.branch 66315
(.branch 66302
(.leaf ⟨66289,13,(.group 4 74 false)⟩)
(.leaf ⟨66302,13,(.group 4 75 false)⟩))
(.branch 66328
(.leaf ⟨66315,13,(.group 4 76 false)⟩)
(.leaf ⟨66328,13,(.group 4 77 false)⟩)))
(.branch 66367
(.branch 66354
(.leaf ⟨66341,13,(.group 4 78 false)⟩)
(.leaf ⟨66354,13,(.group 4 79 false)⟩))
(.branch 66380
(.leaf ⟨66367,13,(.group 4 80 false)⟩)
(.leaf ⟨66380,13,(.group 4 81 false)⟩)))))))

theorem tree66_checked : tree66.check 65561 66393 = true := by decide +kernel

def tree67 : Tree := (.branch 66809
(.branch 66601
(.branch 66497
(.branch 66445
(.branch 66419
(.branch 66406
(.leaf ⟨66393,13,(.group 4 82 false)⟩)
(.leaf ⟨66406,13,(.group 4 83 false)⟩))
(.branch 66432
(.leaf ⟨66419,13,(.group 5 710 false)⟩)
(.leaf ⟨66432,13,(.group 5 711 false)⟩)))
(.branch 66471
(.branch 66458
(.leaf ⟨66445,13,(.group 5 712 false)⟩)
(.leaf ⟨66458,13,(.group 5 713 false)⟩))
(.branch 66484
(.leaf ⟨66471,13,(.group 5 714 false)⟩)
(.leaf ⟨66484,13,(.group 5 715 false)⟩))))
(.branch 66549
(.branch 66523
(.branch 66510
(.leaf ⟨66497,13,(.group 5 716 false)⟩)
(.leaf ⟨66510,13,(.group 5 717 false)⟩))
(.branch 66536
(.leaf ⟨66523,13,(.group 5 718 false)⟩)
(.leaf ⟨66536,13,(.group 5 719 false)⟩)))
(.branch 66575
(.branch 66562
(.leaf ⟨66549,13,(.group 5 720 false)⟩)
(.leaf ⟨66562,13,(.group 5 721 false)⟩))
(.branch 66588
(.leaf ⟨66575,13,(.group 5 722 false)⟩)
(.leaf ⟨66588,13,(.group 5 723 false)⟩)))))
(.branch 66705
(.branch 66653
(.branch 66627
(.branch 66614
(.leaf ⟨66601,13,(.group 5 724 false)⟩)
(.leaf ⟨66614,13,(.group 5 725 false)⟩))
(.branch 66640
(.leaf ⟨66627,13,(.group 5 726 false)⟩)
(.leaf ⟨66640,13,(.group 5 727 false)⟩)))
(.branch 66679
(.branch 66666
(.leaf ⟨66653,13,(.group 5 728 false)⟩)
(.leaf ⟨66666,13,(.group 5 729 false)⟩))
(.branch 66692
(.leaf ⟨66679,13,(.group 5 730 false)⟩)
(.leaf ⟨66692,13,(.group 5 731 false)⟩))))
(.branch 66757
(.branch 66731
(.branch 66718
(.leaf ⟨66705,13,(.group 5 732 false)⟩)
(.leaf ⟨66718,13,(.group 5 733 false)⟩))
(.branch 66744
(.leaf ⟨66731,13,(.group 5 734 false)⟩)
(.leaf ⟨66744,13,(.group 5 735 false)⟩)))
(.branch 66783
(.branch 66770
(.leaf ⟨66757,13,(.group 5 736 false)⟩)
(.leaf ⟨66770,13,(.group 5 737 false)⟩))
(.branch 66796
(.leaf ⟨66783,13,(.group 5 738 false)⟩)
(.leaf ⟨66796,13,(.group 5 739 false)⟩))))))
(.branch 67017
(.branch 66913
(.branch 66861
(.branch 66835
(.branch 66822
(.leaf ⟨66809,13,(.group 5 740 false)⟩)
(.leaf ⟨66822,13,(.group 5 741 false)⟩))
(.branch 66848
(.leaf ⟨66835,13,(.group 5 742 false)⟩)
(.leaf ⟨66848,13,(.group 5 743 false)⟩)))
(.branch 66887
(.branch 66874
(.leaf ⟨66861,13,(.group 5 744 false)⟩)
(.leaf ⟨66874,13,(.group 5 745 false)⟩))
(.branch 66900
(.leaf ⟨66887,13,(.group 5 746 false)⟩)
(.leaf ⟨66900,13,(.group 5 747 false)⟩))))
(.branch 66965
(.branch 66939
(.branch 66926
(.leaf ⟨66913,13,(.group 5 748 false)⟩)
(.leaf ⟨66926,13,(.group 5 749 false)⟩))
(.branch 66952
(.leaf ⟨66939,13,(.group 5 750 false)⟩)
(.leaf ⟨66952,13,(.group 5 751 false)⟩)))
(.branch 66991
(.branch 66978
(.leaf ⟨66965,13,(.group 5 752 false)⟩)
(.leaf ⟨66978,13,(.group 5 753 false)⟩))
(.branch 67004
(.leaf ⟨66991,13,(.group 5 754 false)⟩)
(.leaf ⟨67004,13,(.group 5 755 false)⟩)))))
(.branch 67121
(.branch 67069
(.branch 67043
(.branch 67030
(.leaf ⟨67017,13,(.group 5 756 false)⟩)
(.leaf ⟨67030,13,(.group 5 757 false)⟩))
(.branch 67056
(.leaf ⟨67043,13,(.group 5 758 false)⟩)
(.leaf ⟨67056,13,(.group 5 759 false)⟩)))
(.branch 67095
(.branch 67082
(.leaf ⟨67069,13,(.group 5 760 false)⟩)
(.leaf ⟨67082,13,(.group 5 761 false)⟩))
(.branch 67108
(.leaf ⟨67095,13,(.group 5 762 false)⟩)
(.leaf ⟨67108,13,(.group 5 763 false)⟩))))
(.branch 67173
(.branch 67147
(.branch 67134
(.leaf ⟨67121,13,(.group 5 764 false)⟩)
(.leaf ⟨67134,13,(.group 5 765 false)⟩))
(.branch 67160
(.leaf ⟨67147,13,(.group 5 766 false)⟩)
(.leaf ⟨67160,13,(.group 5 767 false)⟩)))
(.branch 67199
(.branch 67186
(.leaf ⟨67173,13,(.group 5 768 false)⟩)
(.leaf ⟨67186,13,(.group 5 769 false)⟩))
(.branch 67212
(.leaf ⟨67199,13,(.group 5 770 false)⟩)
(.leaf ⟨67212,13,(.group 5 771 false)⟩)))))))

theorem tree67_checked : tree67.check 66393 67225 = true := by decide +kernel

def tree68 : Tree := (.branch 67641
(.branch 67433
(.branch 67329
(.branch 67277
(.branch 67251
(.branch 67238
(.leaf ⟨67225,13,(.group 5 772 false)⟩)
(.leaf ⟨67238,13,(.group 5 773 false)⟩))
(.branch 67264
(.leaf ⟨67251,13,(.group 5 774 false)⟩)
(.leaf ⟨67264,13,(.group 5 775 false)⟩)))
(.branch 67303
(.branch 67290
(.leaf ⟨67277,13,(.group 5 776 false)⟩)
(.leaf ⟨67290,13,(.group 5 777 false)⟩))
(.branch 67316
(.leaf ⟨67303,13,(.group 5 778 false)⟩)
(.leaf ⟨67316,13,(.group 5 779 false)⟩))))
(.branch 67381
(.branch 67355
(.branch 67342
(.leaf ⟨67329,13,(.group 5 780 false)⟩)
(.leaf ⟨67342,13,(.group 5 781 false)⟩))
(.branch 67368
(.leaf ⟨67355,13,(.group 5 782 false)⟩)
(.leaf ⟨67368,13,(.group 5 783 false)⟩)))
(.branch 67407
(.branch 67394
(.leaf ⟨67381,13,(.group 5 784 false)⟩)
(.leaf ⟨67394,13,(.group 5 785 false)⟩))
(.branch 67420
(.leaf ⟨67407,13,(.group 5 786 false)⟩)
(.leaf ⟨67420,13,(.group 5 787 false)⟩)))))
(.branch 67537
(.branch 67485
(.branch 67459
(.branch 67446
(.leaf ⟨67433,13,(.group 5 788 false)⟩)
(.leaf ⟨67446,13,(.group 5 789 false)⟩))
(.branch 67472
(.leaf ⟨67459,13,(.group 5 790 false)⟩)
(.leaf ⟨67472,13,(.group 5 791 false)⟩)))
(.branch 67511
(.branch 67498
(.leaf ⟨67485,13,(.group 5 792 false)⟩)
(.leaf ⟨67498,13,(.group 5 793 false)⟩))
(.branch 67524
(.leaf ⟨67511,13,(.group 5 794 false)⟩)
(.leaf ⟨67524,13,(.group 5 795 false)⟩))))
(.branch 67589
(.branch 67563
(.branch 67550
(.leaf ⟨67537,13,(.group 5 796 false)⟩)
(.leaf ⟨67550,13,(.group 5 797 false)⟩))
(.branch 67576
(.leaf ⟨67563,13,(.group 5 798 false)⟩)
(.leaf ⟨67576,13,(.group 5 799 false)⟩)))
(.branch 67615
(.branch 67602
(.leaf ⟨67589,13,(.group 5 800 false)⟩)
(.leaf ⟨67602,13,(.group 5 801 false)⟩))
(.branch 67628
(.leaf ⟨67615,13,(.group 5 802 false)⟩)
(.leaf ⟨67628,13,(.group 5 803 false)⟩))))))
(.branch 67849
(.branch 67745
(.branch 67693
(.branch 67667
(.branch 67654
(.leaf ⟨67641,13,(.group 5 804 false)⟩)
(.leaf ⟨67654,13,(.group 5 805 false)⟩))
(.branch 67680
(.leaf ⟨67667,13,(.group 5 806 false)⟩)
(.leaf ⟨67680,13,(.group 5 807 false)⟩)))
(.branch 67719
(.branch 67706
(.leaf ⟨67693,13,(.group 5 808 false)⟩)
(.leaf ⟨67706,13,(.group 5 809 false)⟩))
(.branch 67732
(.leaf ⟨67719,13,(.group 5 810 false)⟩)
(.leaf ⟨67732,13,(.group 5 811 false)⟩))))
(.branch 67797
(.branch 67771
(.branch 67758
(.leaf ⟨67745,13,(.group 5 812 false)⟩)
(.leaf ⟨67758,13,(.group 5 813 false)⟩))
(.branch 67784
(.leaf ⟨67771,13,(.group 5 814 false)⟩)
(.leaf ⟨67784,13,(.group 5 815 false)⟩)))
(.branch 67823
(.branch 67810
(.leaf ⟨67797,13,(.group 5 816 false)⟩)
(.leaf ⟨67810,13,(.group 5 817 false)⟩))
(.branch 67836
(.leaf ⟨67823,13,(.group 5 818 false)⟩)
(.leaf ⟨67836,13,(.group 5 819 false)⟩)))))
(.branch 67953
(.branch 67901
(.branch 67875
(.branch 67862
(.leaf ⟨67849,13,(.group 5 820 false)⟩)
(.leaf ⟨67862,13,(.group 5 821 false)⟩))
(.branch 67888
(.leaf ⟨67875,13,(.group 5 822 false)⟩)
(.leaf ⟨67888,13,(.group 5 823 false)⟩)))
(.branch 67927
(.branch 67914
(.leaf ⟨67901,13,(.group 5 824 false)⟩)
(.leaf ⟨67914,13,(.group 5 825 false)⟩))
(.branch 67940
(.leaf ⟨67927,13,(.group 5 826 false)⟩)
(.leaf ⟨67940,13,(.group 5 827 false)⟩))))
(.branch 68005
(.branch 67979
(.branch 67966
(.leaf ⟨67953,13,(.group 5 828 false)⟩)
(.leaf ⟨67966,13,(.group 5 829 false)⟩))
(.branch 67992
(.leaf ⟨67979,13,(.group 6 191 false)⟩)
(.leaf ⟨67992,13,(.group 6 192 false)⟩)))
(.branch 68031
(.branch 68018
(.leaf ⟨68005,13,(.group 6 193 false)⟩)
(.leaf ⟨68018,13,(.group 6 194 false)⟩))
(.branch 68044
(.leaf ⟨68031,13,(.group 6 195 false)⟩)
(.leaf ⟨68044,13,(.group 6 196 false)⟩)))))))

theorem tree68_checked : tree68.check 67225 68057 = true := by decide +kernel

def tree69 : Tree := (.branch 68473
(.branch 68265
(.branch 68161
(.branch 68109
(.branch 68083
(.branch 68070
(.leaf ⟨68057,13,(.group 6 197 false)⟩)
(.leaf ⟨68070,13,(.group 6 198 false)⟩))
(.branch 68096
(.leaf ⟨68083,13,(.group 6 199 false)⟩)
(.leaf ⟨68096,13,(.group 6 200 false)⟩)))
(.branch 68135
(.branch 68122
(.leaf ⟨68109,13,(.group 6 201 false)⟩)
(.leaf ⟨68122,13,(.group 6 202 false)⟩))
(.branch 68148
(.leaf ⟨68135,13,(.group 6 203 false)⟩)
(.leaf ⟨68148,13,(.group 6 204 false)⟩))))
(.branch 68213
(.branch 68187
(.branch 68174
(.leaf ⟨68161,13,(.group 6 205 false)⟩)
(.leaf ⟨68174,13,(.group 6 206 false)⟩))
(.branch 68200
(.leaf ⟨68187,13,(.group 6 207 false)⟩)
(.leaf ⟨68200,13,(.group 6 208 false)⟩)))
(.branch 68239
(.branch 68226
(.leaf ⟨68213,13,(.group 6 209 false)⟩)
(.leaf ⟨68226,13,(.group 6 210 false)⟩))
(.branch 68252
(.leaf ⟨68239,13,(.group 6 211 false)⟩)
(.leaf ⟨68252,13,(.group 6 212 false)⟩)))))
(.branch 68369
(.branch 68317
(.branch 68291
(.branch 68278
(.leaf ⟨68265,13,(.group 6 213 false)⟩)
(.leaf ⟨68278,13,(.group 6 214 false)⟩))
(.branch 68304
(.leaf ⟨68291,13,(.group 6 215 false)⟩)
(.leaf ⟨68304,13,(.group 6 216 false)⟩)))
(.branch 68343
(.branch 68330
(.leaf ⟨68317,13,(.group 6 217 false)⟩)
(.leaf ⟨68330,13,(.group 6 218 false)⟩))
(.branch 68356
(.leaf ⟨68343,13,(.group 6 219 false)⟩)
(.leaf ⟨68356,13,(.group 6 220 false)⟩))))
(.branch 68421
(.branch 68395
(.branch 68382
(.leaf ⟨68369,13,(.group 6 221 false)⟩)
(.leaf ⟨68382,13,(.group 6 222 false)⟩))
(.branch 68408
(.leaf ⟨68395,13,(.group 6 223 false)⟩)
(.leaf ⟨68408,13,(.group 6 224 false)⟩)))
(.branch 68447
(.branch 68434
(.leaf ⟨68421,13,(.group 6 225 false)⟩)
(.leaf ⟨68434,13,(.group 6 226 false)⟩))
(.branch 68460
(.leaf ⟨68447,13,(.group 6 227 false)⟩)
(.leaf ⟨68460,13,(.group 6 228 false)⟩))))))
(.branch 68681
(.branch 68577
(.branch 68525
(.branch 68499
(.branch 68486
(.leaf ⟨68473,13,(.group 6 229 false)⟩)
(.leaf ⟨68486,13,(.group 6 230 false)⟩))
(.branch 68512
(.leaf ⟨68499,13,(.group 6 231 false)⟩)
(.leaf ⟨68512,13,(.group 6 232 false)⟩)))
(.branch 68551
(.branch 68538
(.leaf ⟨68525,13,(.group 6 233 false)⟩)
(.leaf ⟨68538,13,(.group 6 234 false)⟩))
(.branch 68564
(.leaf ⟨68551,13,(.group 6 235 false)⟩)
(.leaf ⟨68564,13,(.group 6 236 false)⟩))))
(.branch 68629
(.branch 68603
(.branch 68590
(.leaf ⟨68577,13,(.group 6 237 false)⟩)
(.leaf ⟨68590,13,(.group 6 238 false)⟩))
(.branch 68616
(.leaf ⟨68603,13,(.group 6 239 false)⟩)
(.leaf ⟨68616,13,(.group 6 240 false)⟩)))
(.branch 68655
(.branch 68642
(.leaf ⟨68629,13,(.group 6 241 false)⟩)
(.leaf ⟨68642,13,(.group 6 242 false)⟩))
(.branch 68668
(.leaf ⟨68655,13,(.group 6 243 false)⟩)
(.leaf ⟨68668,13,(.group 6 244 false)⟩)))))
(.branch 68785
(.branch 68733
(.branch 68707
(.branch 68694
(.leaf ⟨68681,13,(.group 6 245 false)⟩)
(.leaf ⟨68694,13,(.group 6 246 false)⟩))
(.branch 68720
(.leaf ⟨68707,13,(.group 6 247 false)⟩)
(.leaf ⟨68720,13,(.group 6 248 false)⟩)))
(.branch 68759
(.branch 68746
(.leaf ⟨68733,13,(.group 6 249 false)⟩)
(.leaf ⟨68746,13,(.group 6 250 false)⟩))
(.branch 68772
(.leaf ⟨68759,13,(.group 6 251 false)⟩)
(.leaf ⟨68772,13,(.group 6 252 false)⟩))))
(.branch 68837
(.branch 68811
(.branch 68798
(.leaf ⟨68785,13,(.group 6 253 false)⟩)
(.leaf ⟨68798,13,(.group 6 254 false)⟩))
(.branch 68824
(.leaf ⟨68811,13,(.group 6 255 false)⟩)
(.leaf ⟨68824,13,(.group 6 256 false)⟩)))
(.branch 68863
(.branch 68850
(.leaf ⟨68837,13,(.group 6 257 false)⟩)
(.leaf ⟨68850,13,(.group 6 258 false)⟩))
(.branch 68876
(.leaf ⟨68863,13,(.group 6 259 false)⟩)
(.leaf ⟨68876,13,(.group 6 260 false)⟩)))))))

theorem tree69_checked : tree69.check 68057 68889 = true := by decide +kernel

def tree70 : Tree := (.branch 69305
(.branch 69097
(.branch 68993
(.branch 68941
(.branch 68915
(.branch 68902
(.leaf ⟨68889,13,(.group 6 261 false)⟩)
(.leaf ⟨68902,13,(.group 6 262 false)⟩))
(.branch 68928
(.leaf ⟨68915,13,(.group 6 263 false)⟩)
(.leaf ⟨68928,13,(.group 6 264 false)⟩)))
(.branch 68967
(.branch 68954
(.leaf ⟨68941,13,(.group 6 265 false)⟩)
(.leaf ⟨68954,13,(.group 6 266 false)⟩))
(.branch 68980
(.leaf ⟨68967,13,(.group 6 267 false)⟩)
(.leaf ⟨68980,13,(.group 6 268 false)⟩))))
(.branch 69045
(.branch 69019
(.branch 69006
(.leaf ⟨68993,13,(.group 6 269 false)⟩)
(.leaf ⟨69006,13,(.group 6 270 false)⟩))
(.branch 69032
(.leaf ⟨69019,13,(.group 6 271 false)⟩)
(.leaf ⟨69032,13,(.group 6 272 false)⟩)))
(.branch 69071
(.branch 69058
(.leaf ⟨69045,13,(.group 6 273 false)⟩)
(.leaf ⟨69058,13,(.group 6 274 false)⟩))
(.branch 69084
(.leaf ⟨69071,13,(.group 6 275 false)⟩)
(.leaf ⟨69084,13,(.group 6 276 false)⟩)))))
(.branch 69201
(.branch 69149
(.branch 69123
(.branch 69110
(.leaf ⟨69097,13,(.group 6 277 false)⟩)
(.leaf ⟨69110,13,(.group 6 278 false)⟩))
(.branch 69136
(.leaf ⟨69123,13,(.group 6 279 false)⟩)
(.leaf ⟨69136,13,(.group 6 280 false)⟩)))
(.branch 69175
(.branch 69162
(.leaf ⟨69149,13,(.group 6 281 false)⟩)
(.leaf ⟨69162,13,(.group 6 282 false)⟩))
(.branch 69188
(.leaf ⟨69175,13,(.group 6 283 false)⟩)
(.leaf ⟨69188,13,(.group 6 284 false)⟩))))
(.branch 69253
(.branch 69227
(.branch 69214
(.leaf ⟨69201,13,(.group 6 285 false)⟩)
(.leaf ⟨69214,13,(.group 6 286 false)⟩))
(.branch 69240
(.leaf ⟨69227,13,(.group 6 287 false)⟩)
(.leaf ⟨69240,13,(.group 6 288 false)⟩)))
(.branch 69279
(.branch 69266
(.leaf ⟨69253,13,(.group 6 289 false)⟩)
(.leaf ⟨69266,13,(.group 6 290 false)⟩))
(.branch 69292
(.leaf ⟨69279,13,(.group 6 291 false)⟩)
(.leaf ⟨69292,13,(.group 6 292 false)⟩))))))
(.branch 69513
(.branch 69409
(.branch 69357
(.branch 69331
(.branch 69318
(.leaf ⟨69305,13,(.group 6 293 false)⟩)
(.leaf ⟨69318,13,(.group 6 294 false)⟩))
(.branch 69344
(.leaf ⟨69331,13,(.group 6 295 false)⟩)
(.leaf ⟨69344,13,(.group 6 296 false)⟩)))
(.branch 69383
(.branch 69370
(.leaf ⟨69357,13,(.group 6 297 false)⟩)
(.leaf ⟨69370,13,(.group 6 298 false)⟩))
(.branch 69396
(.leaf ⟨69383,13,(.group 6 299 false)⟩)
(.leaf ⟨69396,13,(.group 6 300 false)⟩))))
(.branch 69461
(.branch 69435
(.branch 69422
(.leaf ⟨69409,13,(.group 6 301 false)⟩)
(.leaf ⟨69422,13,(.group 6 302 false)⟩))
(.branch 69448
(.leaf ⟨69435,13,(.group 6 303 false)⟩)
(.leaf ⟨69448,13,(.group 6 304 false)⟩)))
(.branch 69487
(.branch 69474
(.leaf ⟨69461,13,(.group 6 305 false)⟩)
(.leaf ⟨69474,13,(.group 6 306 false)⟩))
(.branch 69500
(.leaf ⟨69487,13,(.group 6 307 false)⟩)
(.leaf ⟨69500,13,(.group 6 308 false)⟩)))))
(.branch 69617
(.branch 69565
(.branch 69539
(.branch 69526
(.leaf ⟨69513,13,(.group 7 82 false)⟩)
(.leaf ⟨69526,13,(.group 7 83 false)⟩))
(.branch 69552
(.leaf ⟨69539,13,(.group 7 84 false)⟩)
(.leaf ⟨69552,13,(.group 7 85 false)⟩)))
(.branch 69591
(.branch 69578
(.leaf ⟨69565,13,(.group 7 86 false)⟩)
(.leaf ⟨69578,13,(.group 7 87 false)⟩))
(.branch 69604
(.leaf ⟨69591,13,(.group 7 88 false)⟩)
(.leaf ⟨69604,13,(.group 7 89 false)⟩))))
(.branch 69669
(.branch 69643
(.branch 69630
(.leaf ⟨69617,13,(.group 7 90 false)⟩)
(.leaf ⟨69630,13,(.group 7 91 false)⟩))
(.branch 69656
(.leaf ⟨69643,13,(.group 7 92 false)⟩)
(.leaf ⟨69656,13,(.group 7 93 false)⟩)))
(.branch 69695
(.branch 69682
(.leaf ⟨69669,13,(.group 7 94 false)⟩)
(.leaf ⟨69682,13,(.group 7 95 false)⟩))
(.branch 69708
(.leaf ⟨69695,13,(.group 7 96 false)⟩)
(.leaf ⟨69708,13,(.group 7 97 false)⟩)))))))

theorem tree70_checked : tree70.check 68889 69721 = true := by decide +kernel

def tree71 : Tree := (.branch 70137
(.branch 69929
(.branch 69825
(.branch 69773
(.branch 69747
(.branch 69734
(.leaf ⟨69721,13,(.group 7 98 false)⟩)
(.leaf ⟨69734,13,(.group 7 99 false)⟩))
(.branch 69760
(.leaf ⟨69747,13,(.group 7 100 false)⟩)
(.leaf ⟨69760,13,(.group 7 101 false)⟩)))
(.branch 69799
(.branch 69786
(.leaf ⟨69773,13,(.group 7 102 false)⟩)
(.leaf ⟨69786,13,(.group 7 103 false)⟩))
(.branch 69812
(.leaf ⟨69799,13,(.group 7 104 false)⟩)
(.leaf ⟨69812,13,(.group 7 105 false)⟩))))
(.branch 69877
(.branch 69851
(.branch 69838
(.leaf ⟨69825,13,(.group 7 106 false)⟩)
(.leaf ⟨69838,13,(.group 7 107 false)⟩))
(.branch 69864
(.leaf ⟨69851,13,(.group 7 108 false)⟩)
(.leaf ⟨69864,13,(.group 7 109 false)⟩)))
(.branch 69903
(.branch 69890
(.leaf ⟨69877,13,(.group 7 110 false)⟩)
(.leaf ⟨69890,13,(.group 7 111 false)⟩))
(.branch 69916
(.leaf ⟨69903,13,(.group 8 124 false)⟩)
(.leaf ⟨69916,13,(.group 8 125 false)⟩)))))
(.branch 70033
(.branch 69981
(.branch 69955
(.branch 69942
(.leaf ⟨69929,13,(.group 8 126 false)⟩)
(.leaf ⟨69942,13,(.group 8 127 false)⟩))
(.branch 69968
(.leaf ⟨69955,13,(.group 8 128 false)⟩)
(.leaf ⟨69968,13,(.group 8 129 false)⟩)))
(.branch 70007
(.branch 69994
(.leaf ⟨69981,13,(.group 8 130 false)⟩)
(.leaf ⟨69994,13,(.group 8 131 false)⟩))
(.branch 70020
(.leaf ⟨70007,13,(.group 8 132 false)⟩)
(.leaf ⟨70020,13,(.group 8 133 false)⟩))))
(.branch 70085
(.branch 70059
(.branch 70046
(.leaf ⟨70033,13,(.group 8 134 false)⟩)
(.leaf ⟨70046,13,(.group 8 135 false)⟩))
(.branch 70072
(.leaf ⟨70059,13,(.group 8 136 false)⟩)
(.leaf ⟨70072,13,(.group 8 137 false)⟩)))
(.branch 70111
(.branch 70098
(.leaf ⟨70085,13,(.group 8 138 false)⟩)
(.leaf ⟨70098,13,(.group 8 139 false)⟩))
(.branch 70124
(.leaf ⟨70111,13,(.group 8 140 false)⟩)
(.leaf ⟨70124,13,(.group 8 141 false)⟩))))))
(.branch 70345
(.branch 70241
(.branch 70189
(.branch 70163
(.branch 70150
(.leaf ⟨70137,13,(.group 8 142 false)⟩)
(.leaf ⟨70150,13,(.group 8 143 false)⟩))
(.branch 70176
(.leaf ⟨70163,13,(.group 8 144 false)⟩)
(.leaf ⟨70176,13,(.group 8 145 false)⟩)))
(.branch 70215
(.branch 70202
(.leaf ⟨70189,13,(.group 8 146 false)⟩)
(.leaf ⟨70202,13,(.group 8 147 false)⟩))
(.branch 70228
(.leaf ⟨70215,13,(.group 8 148 false)⟩)
(.leaf ⟨70228,13,(.group 8 149 false)⟩))))
(.branch 70293
(.branch 70267
(.branch 70254
(.leaf ⟨70241,13,(.group 8 150 false)⟩)
(.leaf ⟨70254,13,(.group 8 151 false)⟩))
(.branch 70280
(.leaf ⟨70267,13,(.group 8 152 false)⟩)
(.leaf ⟨70280,13,(.group 8 153 false)⟩)))
(.branch 70319
(.branch 70306
(.leaf ⟨70293,13,(.group 8 154 false)⟩)
(.leaf ⟨70306,13,(.group 8 155 false)⟩))
(.branch 70332
(.leaf ⟨70319,13,(.group 8 156 false)⟩)
(.leaf ⟨70332,13,(.group 9 120 false)⟩)))))
(.branch 70449
(.branch 70397
(.branch 70371
(.branch 70358
(.leaf ⟨70345,13,(.group 9 121 false)⟩)
(.leaf ⟨70358,13,(.group 9 122 false)⟩))
(.branch 70384
(.leaf ⟨70371,13,(.group 9 123 false)⟩)
(.leaf ⟨70384,13,(.group 9 124 false)⟩)))
(.branch 70423
(.branch 70410
(.leaf ⟨70397,13,(.group 9 125 false)⟩)
(.leaf ⟨70410,13,(.group 9 126 false)⟩))
(.branch 70436
(.leaf ⟨70423,13,(.group 9 127 false)⟩)
(.leaf ⟨70436,13,(.group 9 128 false)⟩))))
(.branch 70501
(.branch 70475
(.branch 70462
(.leaf ⟨70449,13,(.group 9 129 false)⟩)
(.leaf ⟨70462,13,(.group 9 130 false)⟩))
(.branch 70488
(.leaf ⟨70475,13,(.group 9 131 false)⟩)
(.leaf ⟨70488,13,(.group 9 132 false)⟩)))
(.branch 70527
(.branch 70514
(.leaf ⟨70501,13,(.group 9 133 false)⟩)
(.leaf ⟨70514,13,(.group 9 134 false)⟩))
(.branch 70540
(.leaf ⟨70527,13,(.group 9 135 false)⟩)
(.leaf ⟨70540,13,(.group 9 136 false)⟩)))))))

theorem tree71_checked : tree71.check 69721 70553 = true := by decide +kernel

def tree72 : Tree := (.branch 70985
(.branch 70761
(.branch 70657
(.branch 70605
(.branch 70579
(.branch 70566
(.leaf ⟨70553,13,(.group 9 137 false)⟩)
(.leaf ⟨70566,13,(.group 9 138 false)⟩))
(.branch 70592
(.leaf ⟨70579,13,(.group 9 139 false)⟩)
(.leaf ⟨70592,13,(.group 9 140 false)⟩)))
(.branch 70631
(.branch 70618
(.leaf ⟨70605,13,(.group 9 141 false)⟩)
(.leaf ⟨70618,13,(.group 9 142 false)⟩))
(.branch 70644
(.leaf ⟨70631,13,(.group 9 143 false)⟩)
(.leaf ⟨70644,13,(.group 9 144 false)⟩))))
(.branch 70709
(.branch 70683
(.branch 70670
(.leaf ⟨70657,13,(.group 9 145 false)⟩)
(.leaf ⟨70670,13,(.group 9 146 false)⟩))
(.branch 70696
(.leaf ⟨70683,13,(.group 9 147 false)⟩)
(.leaf ⟨70696,13,(.group 9 148 false)⟩)))
(.branch 70735
(.branch 70722
(.leaf ⟨70709,13,(.group 9 149 false)⟩)
(.leaf ⟨70722,13,(.group 9 150 false)⟩))
(.branch 70748
(.leaf ⟨70735,13,(.group 9 151 false)⟩)
(.leaf ⟨70748,13,(.group 9 152 false)⟩)))))
(.branch 70873
(.branch 70817
(.branch 70789
(.branch 70775
(.leaf ⟨70761,14,(.group 0 238 false)⟩)
(.leaf ⟨70775,14,(.group 0 239 false)⟩))
(.branch 70803
(.leaf ⟨70789,14,(.group 0 240 false)⟩)
(.leaf ⟨70803,14,(.group 0 241 false)⟩)))
(.branch 70845
(.branch 70831
(.leaf ⟨70817,14,(.group 0 242 false)⟩)
(.leaf ⟨70831,14,(.group 0 243 false)⟩))
(.branch 70859
(.leaf ⟨70845,14,(.group 0 244 false)⟩)
(.leaf ⟨70859,14,(.group 0 245 false)⟩))))
(.branch 70929
(.branch 70901
(.branch 70887
(.leaf ⟨70873,14,(.group 0 246 false)⟩)
(.leaf ⟨70887,14,(.group 0 247 false)⟩))
(.branch 70915
(.leaf ⟨70901,14,(.group 0 248 false)⟩)
(.leaf ⟨70915,14,(.group 0 249 false)⟩)))
(.branch 70957
(.branch 70943
(.leaf ⟨70929,14,(.group 0 250 false)⟩)
(.leaf ⟨70943,14,(.group 0 251 false)⟩))
(.branch 70971
(.leaf ⟨70957,14,(.group 0 252 false)⟩)
(.leaf ⟨70971,14,(.group 0 253 false)⟩))))))
(.branch 71209
(.branch 71097
(.branch 71041
(.branch 71013
(.branch 70999
(.leaf ⟨70985,14,(.group 0 254 false)⟩)
(.leaf ⟨70999,14,(.group 0 255 false)⟩))
(.branch 71027
(.leaf ⟨71013,14,(.group 0 256 false)⟩)
(.leaf ⟨71027,14,(.group 0 257 false)⟩)))
(.branch 71069
(.branch 71055
(.leaf ⟨71041,14,(.group 0 258 false)⟩)
(.leaf ⟨71055,14,(.group 0 259 false)⟩))
(.branch 71083
(.leaf ⟨71069,14,(.group 0 260 false)⟩)
(.leaf ⟨71083,14,(.group 0 261 false)⟩))))
(.branch 71153
(.branch 71125
(.branch 71111
(.leaf ⟨71097,14,(.group 0 262 false)⟩)
(.leaf ⟨71111,14,(.group 0 263 false)⟩))
(.branch 71139
(.leaf ⟨71125,14,(.group 0 264 false)⟩)
(.leaf ⟨71139,14,(.group 0 265 false)⟩)))
(.branch 71181
(.branch 71167
(.leaf ⟨71153,14,(.group 0 266 false)⟩)
(.leaf ⟨71167,14,(.group 0 267 false)⟩))
(.branch 71195
(.leaf ⟨71181,14,(.group 0 268 false)⟩)
(.leaf ⟨71195,14,(.group 0 269 false)⟩)))))
(.branch 71321
(.branch 71265
(.branch 71237
(.branch 71223
(.leaf ⟨71209,14,(.group 0 270 false)⟩)
(.leaf ⟨71223,14,(.group 0 271 false)⟩))
(.branch 71251
(.leaf ⟨71237,14,(.group 0 272 false)⟩)
(.leaf ⟨71251,14,(.group 0 273 false)⟩)))
(.branch 71293
(.branch 71279
(.leaf ⟨71265,14,(.group 0 274 false)⟩)
(.leaf ⟨71279,14,(.group 0 275 false)⟩))
(.branch 71307
(.leaf ⟨71293,14,(.group 0 276 false)⟩)
(.leaf ⟨71307,14,(.group 0 277 false)⟩))))
(.branch 71377
(.branch 71349
(.branch 71335
(.leaf ⟨71321,14,(.group 0 278 false)⟩)
(.leaf ⟨71335,14,(.group 0 279 false)⟩))
(.branch 71363
(.leaf ⟨71349,14,(.group 0 280 false)⟩)
(.leaf ⟨71363,14,(.group 0 281 false)⟩)))
(.branch 71405
(.branch 71391
(.leaf ⟨71377,14,(.group 0 282 false)⟩)
(.leaf ⟨71391,14,(.group 0 283 false)⟩))
(.branch 71419
(.leaf ⟨71405,14,(.group 0 284 false)⟩)
(.leaf ⟨71419,14,(.group 0 285 false)⟩)))))))

theorem tree72_checked : tree72.check 70553 71433 = true := by decide +kernel

def tree73 : Tree := (.branch 71881
(.branch 71657
(.branch 71545
(.branch 71489
(.branch 71461
(.branch 71447
(.leaf ⟨71433,14,(.group 0 286 false)⟩)
(.leaf ⟨71447,14,(.group 0 287 false)⟩))
(.branch 71475
(.leaf ⟨71461,14,(.group 0 288 false)⟩)
(.leaf ⟨71475,14,(.group 0 289 false)⟩)))
(.branch 71517
(.branch 71503
(.leaf ⟨71489,14,(.group 0 290 false)⟩)
(.leaf ⟨71503,14,(.group 0 291 false)⟩))
(.branch 71531
(.leaf ⟨71517,14,(.group 0 292 false)⟩)
(.leaf ⟨71531,14,(.group 0 293 false)⟩))))
(.branch 71601
(.branch 71573
(.branch 71559
(.leaf ⟨71545,14,(.group 0 294 false)⟩)
(.leaf ⟨71559,14,(.group 0 295 false)⟩))
(.branch 71587
(.leaf ⟨71573,14,(.group 0 296 false)⟩)
(.leaf ⟨71587,14,(.group 0 297 false)⟩)))
(.branch 71629
(.branch 71615
(.leaf ⟨71601,14,(.group 0 298 false)⟩)
(.leaf ⟨71615,14,(.group 0 299 false)⟩))
(.branch 71643
(.leaf ⟨71629,14,(.group 0 300 false)⟩)
(.leaf ⟨71643,14,(.group 0 301 false)⟩)))))
(.branch 71769
(.branch 71713
(.branch 71685
(.branch 71671
(.leaf ⟨71657,14,(.group 0 302 false)⟩)
(.leaf ⟨71671,14,(.group 0 303 false)⟩))
(.branch 71699
(.leaf ⟨71685,14,(.group 0 304 false)⟩)
(.leaf ⟨71699,14,(.group 0 305 false)⟩)))
(.branch 71741
(.branch 71727
(.leaf ⟨71713,14,(.group 0 306 false)⟩)
(.leaf ⟨71727,14,(.group 0 307 false)⟩))
(.branch 71755
(.leaf ⟨71741,14,(.group 0 308 false)⟩)
(.leaf ⟨71755,14,(.group 0 309 false)⟩))))
(.branch 71825
(.branch 71797
(.branch 71783
(.leaf ⟨71769,14,(.group 0 310 false)⟩)
(.leaf ⟨71783,14,(.group 0 311 false)⟩))
(.branch 71811
(.leaf ⟨71797,14,(.group 0 312 false)⟩)
(.leaf ⟨71811,14,(.group 0 313 false)⟩)))
(.branch 71853
(.branch 71839
(.leaf ⟨71825,14,(.group 0 314 false)⟩)
(.leaf ⟨71839,14,(.group 0 315 false)⟩))
(.branch 71867
(.leaf ⟨71853,14,(.group 0 316 false)⟩)
(.leaf ⟨71867,14,(.group 0 317 false)⟩))))))
(.branch 72105
(.branch 71993
(.branch 71937
(.branch 71909
(.branch 71895
(.leaf ⟨71881,14,(.group 0 318 false)⟩)
(.leaf ⟨71895,14,(.group 0 319 false)⟩))
(.branch 71923
(.leaf ⟨71909,14,(.group 0 320 false)⟩)
(.leaf ⟨71923,14,(.group 0 321 false)⟩)))
(.branch 71965
(.branch 71951
(.leaf ⟨71937,14,(.group 0 322 false)⟩)
(.leaf ⟨71951,14,(.group 0 323 false)⟩))
(.branch 71979
(.leaf ⟨71965,14,(.group 0 324 false)⟩)
(.leaf ⟨71979,14,(.group 0 325 false)⟩))))
(.branch 72049
(.branch 72021
(.branch 72007
(.leaf ⟨71993,14,(.group 0 326 false)⟩)
(.leaf ⟨72007,14,(.group 0 327 false)⟩))
(.branch 72035
(.leaf ⟨72021,14,(.group 1 84 false)⟩)
(.leaf ⟨72035,14,(.group 1 85 false)⟩)))
(.branch 72077
(.branch 72063
(.leaf ⟨72049,14,(.group 1 86 false)⟩)
(.leaf ⟨72063,14,(.group 1 87 false)⟩))
(.branch 72091
(.leaf ⟨72077,14,(.group 1 88 false)⟩)
(.leaf ⟨72091,14,(.group 1 89 false)⟩)))))
(.branch 72217
(.branch 72161
(.branch 72133
(.branch 72119
(.leaf ⟨72105,14,(.group 1 90 false)⟩)
(.leaf ⟨72119,14,(.group 1 91 false)⟩))
(.branch 72147
(.leaf ⟨72133,14,(.group 1 92 false)⟩)
(.leaf ⟨72147,14,(.group 1 93 false)⟩)))
(.branch 72189
(.branch 72175
(.leaf ⟨72161,14,(.group 1 94 false)⟩)
(.leaf ⟨72175,14,(.group 1 95 false)⟩))
(.branch 72203
(.leaf ⟨72189,14,(.group 1 96 false)⟩)
(.leaf ⟨72203,14,(.group 1 97 false)⟩))))
(.branch 72273
(.branch 72245
(.branch 72231
(.leaf ⟨72217,14,(.group 1 98 false)⟩)
(.leaf ⟨72231,14,(.group 1 99 false)⟩))
(.branch 72259
(.leaf ⟨72245,14,(.group 1 100 false)⟩)
(.leaf ⟨72259,14,(.group 1 101 false)⟩)))
(.branch 72301
(.branch 72287
(.leaf ⟨72273,14,(.group 1 102 false)⟩)
(.leaf ⟨72287,14,(.group 1 103 false)⟩))
(.branch 72315
(.leaf ⟨72301,14,(.group 1 104 false)⟩)
(.leaf ⟨72315,14,(.group 1 105 false)⟩)))))))

theorem tree73_checked : tree73.check 71433 72329 = true := by decide +kernel

def tree74 : Tree := (.branch 72777
(.branch 72553
(.branch 72441
(.branch 72385
(.branch 72357
(.branch 72343
(.leaf ⟨72329,14,(.group 1 106 false)⟩)
(.leaf ⟨72343,14,(.group 1 107 false)⟩))
(.branch 72371
(.leaf ⟨72357,14,(.group 1 108 false)⟩)
(.leaf ⟨72371,14,(.group 1 109 false)⟩)))
(.branch 72413
(.branch 72399
(.leaf ⟨72385,14,(.group 1 110 false)⟩)
(.leaf ⟨72399,14,(.group 1 111 false)⟩))
(.branch 72427
(.leaf ⟨72413,14,(.group 1 112 false)⟩)
(.leaf ⟨72427,14,(.group 1 113 false)⟩))))
(.branch 72497
(.branch 72469
(.branch 72455
(.leaf ⟨72441,14,(.group 1 114 false)⟩)
(.leaf ⟨72455,14,(.group 1 115 false)⟩))
(.branch 72483
(.leaf ⟨72469,14,(.group 1 116 false)⟩)
(.leaf ⟨72483,14,(.group 1 117 false)⟩)))
(.branch 72525
(.branch 72511
(.leaf ⟨72497,14,(.group 1 118 false)⟩)
(.leaf ⟨72511,14,(.group 1 119 false)⟩))
(.branch 72539
(.leaf ⟨72525,14,(.group 2 84 false)⟩)
(.leaf ⟨72539,14,(.group 2 85 false)⟩)))))
(.branch 72665
(.branch 72609
(.branch 72581
(.branch 72567
(.leaf ⟨72553,14,(.group 2 86 false)⟩)
(.leaf ⟨72567,14,(.group 2 87 false)⟩))
(.branch 72595
(.leaf ⟨72581,14,(.group 2 88 false)⟩)
(.leaf ⟨72595,14,(.group 2 89 false)⟩)))
(.branch 72637
(.branch 72623
(.leaf ⟨72609,14,(.group 2 90 false)⟩)
(.leaf ⟨72623,14,(.group 2 91 false)⟩))
(.branch 72651
(.leaf ⟨72637,14,(.group 2 92 false)⟩)
(.leaf ⟨72651,14,(.group 2 93 false)⟩))))
(.branch 72721
(.branch 72693
(.branch 72679
(.leaf ⟨72665,14,(.group 2 94 false)⟩)
(.leaf ⟨72679,14,(.group 2 95 false)⟩))
(.branch 72707
(.leaf ⟨72693,14,(.group 2 96 false)⟩)
(.leaf ⟨72707,14,(.group 2 97 false)⟩)))
(.branch 72749
(.branch 72735
(.leaf ⟨72721,14,(.group 2 98 false)⟩)
(.leaf ⟨72735,14,(.group 2 99 false)⟩))
(.branch 72763
(.leaf ⟨72749,14,(.group 2 100 false)⟩)
(.leaf ⟨72763,14,(.group 2 101 false)⟩))))))
(.branch 73001
(.branch 72889
(.branch 72833
(.branch 72805
(.branch 72791
(.leaf ⟨72777,14,(.group 2 102 false)⟩)
(.leaf ⟨72791,14,(.group 2 103 false)⟩))
(.branch 72819
(.leaf ⟨72805,14,(.group 2 104 false)⟩)
(.leaf ⟨72819,14,(.group 2 105 false)⟩)))
(.branch 72861
(.branch 72847
(.leaf ⟨72833,14,(.group 2 106 false)⟩)
(.leaf ⟨72847,14,(.group 2 107 false)⟩))
(.branch 72875
(.leaf ⟨72861,14,(.group 2 108 false)⟩)
(.leaf ⟨72875,14,(.group 2 109 false)⟩))))
(.branch 72945
(.branch 72917
(.branch 72903
(.leaf ⟨72889,14,(.group 2 110 false)⟩)
(.leaf ⟨72903,14,(.group 2 111 false)⟩))
(.branch 72931
(.leaf ⟨72917,14,(.group 2 112 false)⟩)
(.leaf ⟨72931,14,(.group 2 113 false)⟩)))
(.branch 72973
(.branch 72959
(.leaf ⟨72945,14,(.group 2 114 false)⟩)
(.leaf ⟨72959,14,(.group 2 115 false)⟩))
(.branch 72987
(.leaf ⟨72973,14,(.group 2 116 false)⟩)
(.leaf ⟨72987,14,(.group 2 117 false)⟩)))))
(.branch 73113
(.branch 73057
(.branch 73029
(.branch 73015
(.leaf ⟨73001,14,(.group 2 118 false)⟩)
(.leaf ⟨73015,14,(.group 2 119 false)⟩))
(.branch 73043
(.leaf ⟨73029,14,(.group 3 84 false)⟩)
(.leaf ⟨73043,14,(.group 3 85 false)⟩)))
(.branch 73085
(.branch 73071
(.leaf ⟨73057,14,(.group 3 86 false)⟩)
(.leaf ⟨73071,14,(.group 3 87 false)⟩))
(.branch 73099
(.leaf ⟨73085,14,(.group 3 88 false)⟩)
(.leaf ⟨73099,14,(.group 3 89 false)⟩))))
(.branch 73169
(.branch 73141
(.branch 73127
(.leaf ⟨73113,14,(.group 3 90 false)⟩)
(.leaf ⟨73127,14,(.group 3 91 false)⟩))
(.branch 73155
(.leaf ⟨73141,14,(.group 3 92 false)⟩)
(.leaf ⟨73155,14,(.group 3 93 false)⟩)))
(.branch 73197
(.branch 73183
(.leaf ⟨73169,14,(.group 3 94 false)⟩)
(.leaf ⟨73183,14,(.group 3 95 false)⟩))
(.branch 73211
(.leaf ⟨73197,14,(.group 3 96 false)⟩)
(.leaf ⟨73211,14,(.group 3 97 false)⟩)))))))

theorem tree74_checked : tree74.check 72329 73225 = true := by decide +kernel

def tree75 : Tree := (.branch 73673
(.branch 73449
(.branch 73337
(.branch 73281
(.branch 73253
(.branch 73239
(.leaf ⟨73225,14,(.group 3 98 false)⟩)
(.leaf ⟨73239,14,(.group 3 99 false)⟩))
(.branch 73267
(.leaf ⟨73253,14,(.group 3 100 false)⟩)
(.leaf ⟨73267,14,(.group 3 101 false)⟩)))
(.branch 73309
(.branch 73295
(.leaf ⟨73281,14,(.group 3 102 false)⟩)
(.leaf ⟨73295,14,(.group 3 103 false)⟩))
(.branch 73323
(.leaf ⟨73309,14,(.group 3 104 false)⟩)
(.leaf ⟨73323,14,(.group 3 105 false)⟩))))
(.branch 73393
(.branch 73365
(.branch 73351
(.leaf ⟨73337,14,(.group 3 106 false)⟩)
(.leaf ⟨73351,14,(.group 3 107 false)⟩))
(.branch 73379
(.leaf ⟨73365,14,(.group 3 108 false)⟩)
(.leaf ⟨73379,14,(.group 3 109 false)⟩)))
(.branch 73421
(.branch 73407
(.leaf ⟨73393,14,(.group 3 110 false)⟩)
(.leaf ⟨73407,14,(.group 3 111 false)⟩))
(.branch 73435
(.leaf ⟨73421,14,(.group 3 112 false)⟩)
(.leaf ⟨73435,14,(.group 3 113 false)⟩)))))
(.branch 73561
(.branch 73505
(.branch 73477
(.branch 73463
(.leaf ⟨73449,14,(.group 3 114 false)⟩)
(.leaf ⟨73463,14,(.group 3 115 false)⟩))
(.branch 73491
(.leaf ⟨73477,14,(.group 3 116 false)⟩)
(.leaf ⟨73491,14,(.group 3 117 false)⟩)))
(.branch 73533
(.branch 73519
(.leaf ⟨73505,14,(.group 3 118 false)⟩)
(.leaf ⟨73519,14,(.group 3 119 false)⟩))
(.branch 73547
(.leaf ⟨73533,14,(.group 4 84 false)⟩)
(.leaf ⟨73547,14,(.group 4 85 false)⟩))))
(.branch 73617
(.branch 73589
(.branch 73575
(.leaf ⟨73561,14,(.group 4 86 false)⟩)
(.leaf ⟨73575,14,(.group 4 87 false)⟩))
(.branch 73603
(.leaf ⟨73589,14,(.group 4 88 false)⟩)
(.leaf ⟨73603,14,(.group 4 89 false)⟩)))
(.branch 73645
(.branch 73631
(.leaf ⟨73617,14,(.group 4 90 false)⟩)
(.leaf ⟨73631,14,(.group 4 91 false)⟩))
(.branch 73659
(.leaf ⟨73645,14,(.group 4 92 false)⟩)
(.leaf ⟨73659,14,(.group 4 93 false)⟩))))))
(.branch 73897
(.branch 73785
(.branch 73729
(.branch 73701
(.branch 73687
(.leaf ⟨73673,14,(.group 4 94 false)⟩)
(.leaf ⟨73687,14,(.group 4 95 false)⟩))
(.branch 73715
(.leaf ⟨73701,14,(.group 4 96 false)⟩)
(.leaf ⟨73715,14,(.group 4 97 false)⟩)))
(.branch 73757
(.branch 73743
(.leaf ⟨73729,14,(.group 4 98 false)⟩)
(.leaf ⟨73743,14,(.group 4 99 false)⟩))
(.branch 73771
(.leaf ⟨73757,14,(.group 4 100 false)⟩)
(.leaf ⟨73771,14,(.group 4 101 false)⟩))))
(.branch 73841
(.branch 73813
(.branch 73799
(.leaf ⟨73785,14,(.group 4 102 false)⟩)
(.leaf ⟨73799,14,(.group 4 103 false)⟩))
(.branch 73827
(.leaf ⟨73813,14,(.group 4 104 false)⟩)
(.leaf ⟨73827,14,(.group 4 105 false)⟩)))
(.branch 73869
(.branch 73855
(.leaf ⟨73841,14,(.group 4 106 false)⟩)
(.leaf ⟨73855,14,(.group 4 107 false)⟩))
(.branch 73883
(.leaf ⟨73869,14,(.group 4 108 false)⟩)
(.leaf ⟨73883,14,(.group 4 109 false)⟩)))))
(.branch 74009
(.branch 73953
(.branch 73925
(.branch 73911
(.leaf ⟨73897,14,(.group 4 110 false)⟩)
(.leaf ⟨73911,14,(.group 4 111 false)⟩))
(.branch 73939
(.leaf ⟨73925,14,(.group 4 112 false)⟩)
(.leaf ⟨73939,14,(.group 4 113 false)⟩)))
(.branch 73981
(.branch 73967
(.leaf ⟨73953,14,(.group 4 114 false)⟩)
(.leaf ⟨73967,14,(.group 4 115 false)⟩))
(.branch 73995
(.leaf ⟨73981,14,(.group 4 116 false)⟩)
(.leaf ⟨73995,14,(.group 4 117 false)⟩))))
(.branch 74065
(.branch 74037
(.branch 74023
(.leaf ⟨74009,14,(.group 4 118 false)⟩)
(.leaf ⟨74023,14,(.group 4 119 false)⟩))
(.branch 74051
(.leaf ⟨74037,14,(.group 5 830 false)⟩)
(.leaf ⟨74051,14,(.group 5 831 false)⟩)))
(.branch 74093
(.branch 74079
(.leaf ⟨74065,14,(.group 5 832 false)⟩)
(.leaf ⟨74079,14,(.group 5 833 false)⟩))
(.branch 74107
(.leaf ⟨74093,14,(.group 5 834 false)⟩)
(.leaf ⟨74107,14,(.group 5 835 false)⟩)))))))

theorem tree75_checked : tree75.check 73225 74121 = true := by decide +kernel

def tree76 : Tree := (.branch 74569
(.branch 74345
(.branch 74233
(.branch 74177
(.branch 74149
(.branch 74135
(.leaf ⟨74121,14,(.group 5 836 false)⟩)
(.leaf ⟨74135,14,(.group 5 837 false)⟩))
(.branch 74163
(.leaf ⟨74149,14,(.group 5 838 false)⟩)
(.leaf ⟨74163,14,(.group 5 839 false)⟩)))
(.branch 74205
(.branch 74191
(.leaf ⟨74177,14,(.group 5 840 false)⟩)
(.leaf ⟨74191,14,(.group 5 841 false)⟩))
(.branch 74219
(.leaf ⟨74205,14,(.group 5 842 false)⟩)
(.leaf ⟨74219,14,(.group 5 843 false)⟩))))
(.branch 74289
(.branch 74261
(.branch 74247
(.leaf ⟨74233,14,(.group 5 844 false)⟩)
(.leaf ⟨74247,14,(.group 5 845 false)⟩))
(.branch 74275
(.leaf ⟨74261,14,(.group 5 846 false)⟩)
(.leaf ⟨74275,14,(.group 5 847 false)⟩)))
(.branch 74317
(.branch 74303
(.leaf ⟨74289,14,(.group 5 848 false)⟩)
(.leaf ⟨74303,14,(.group 5 849 false)⟩))
(.branch 74331
(.leaf ⟨74317,14,(.group 5 850 false)⟩)
(.leaf ⟨74331,14,(.group 5 851 false)⟩)))))
(.branch 74457
(.branch 74401
(.branch 74373
(.branch 74359
(.leaf ⟨74345,14,(.group 5 852 false)⟩)
(.leaf ⟨74359,14,(.group 5 853 false)⟩))
(.branch 74387
(.leaf ⟨74373,14,(.group 5 854 false)⟩)
(.leaf ⟨74387,14,(.group 5 855 false)⟩)))
(.branch 74429
(.branch 74415
(.leaf ⟨74401,14,(.group 5 856 false)⟩)
(.leaf ⟨74415,14,(.group 5 857 false)⟩))
(.branch 74443
(.leaf ⟨74429,14,(.group 5 858 false)⟩)
(.leaf ⟨74443,14,(.group 5 859 false)⟩))))
(.branch 74513
(.branch 74485
(.branch 74471
(.leaf ⟨74457,14,(.group 5 860 false)⟩)
(.leaf ⟨74471,14,(.group 5 861 false)⟩))
(.branch 74499
(.leaf ⟨74485,14,(.group 5 862 false)⟩)
(.leaf ⟨74499,14,(.group 5 863 false)⟩)))
(.branch 74541
(.branch 74527
(.leaf ⟨74513,14,(.group 5 864 false)⟩)
(.leaf ⟨74527,14,(.group 5 865 false)⟩))
(.branch 74555
(.leaf ⟨74541,14,(.group 5 866 false)⟩)
(.leaf ⟨74555,14,(.group 5 867 false)⟩))))))
(.branch 74793
(.branch 74681
(.branch 74625
(.branch 74597
(.branch 74583
(.leaf ⟨74569,14,(.group 5 868 false)⟩)
(.leaf ⟨74583,14,(.group 5 869 false)⟩))
(.branch 74611
(.leaf ⟨74597,14,(.group 5 870 false)⟩)
(.leaf ⟨74611,14,(.group 5 871 false)⟩)))
(.branch 74653
(.branch 74639
(.leaf ⟨74625,14,(.group 5 872 false)⟩)
(.leaf ⟨74639,14,(.group 5 873 false)⟩))
(.branch 74667
(.leaf ⟨74653,14,(.group 5 874 false)⟩)
(.leaf ⟨74667,14,(.group 5 875 false)⟩))))
(.branch 74737
(.branch 74709
(.branch 74695
(.leaf ⟨74681,14,(.group 5 876 false)⟩)
(.leaf ⟨74695,14,(.group 5 877 false)⟩))
(.branch 74723
(.leaf ⟨74709,14,(.group 5 878 false)⟩)
(.leaf ⟨74723,14,(.group 5 879 false)⟩)))
(.branch 74765
(.branch 74751
(.leaf ⟨74737,14,(.group 5 880 false)⟩)
(.leaf ⟨74751,14,(.group 5 881 false)⟩))
(.branch 74779
(.leaf ⟨74765,14,(.group 5 882 false)⟩)
(.leaf ⟨74779,14,(.group 5 883 false)⟩)))))
(.branch 74905
(.branch 74849
(.branch 74821
(.branch 74807
(.leaf ⟨74793,14,(.group 5 884 false)⟩)
(.leaf ⟨74807,14,(.group 5 885 false)⟩))
(.branch 74835
(.leaf ⟨74821,14,(.group 5 886 false)⟩)
(.leaf ⟨74835,14,(.group 5 887 false)⟩)))
(.branch 74877
(.branch 74863
(.leaf ⟨74849,14,(.group 5 888 false)⟩)
(.leaf ⟨74863,14,(.group 5 889 false)⟩))
(.branch 74891
(.leaf ⟨74877,14,(.group 5 890 false)⟩)
(.leaf ⟨74891,14,(.group 5 891 false)⟩))))
(.branch 74961
(.branch 74933
(.branch 74919
(.leaf ⟨74905,14,(.group 5 892 false)⟩)
(.leaf ⟨74919,14,(.group 5 893 false)⟩))
(.branch 74947
(.leaf ⟨74933,14,(.group 5 894 false)⟩)
(.leaf ⟨74947,14,(.group 5 895 false)⟩)))
(.branch 74989
(.branch 74975
(.leaf ⟨74961,14,(.group 5 896 false)⟩)
(.leaf ⟨74975,14,(.group 5 897 false)⟩))
(.branch 75003
(.leaf ⟨74989,14,(.group 5 898 false)⟩)
(.leaf ⟨75003,14,(.group 5 899 false)⟩)))))))

theorem tree76_checked : tree76.check 74121 75017 = true := by decide +kernel

def tree77 : Tree := (.branch 75465
(.branch 75241
(.branch 75129
(.branch 75073
(.branch 75045
(.branch 75031
(.leaf ⟨75017,14,(.group 5 900 false)⟩)
(.leaf ⟨75031,14,(.group 5 901 false)⟩))
(.branch 75059
(.leaf ⟨75045,14,(.group 5 902 false)⟩)
(.leaf ⟨75059,14,(.group 5 903 false)⟩)))
(.branch 75101
(.branch 75087
(.leaf ⟨75073,14,(.group 5 904 false)⟩)
(.leaf ⟨75087,14,(.group 5 905 false)⟩))
(.branch 75115
(.leaf ⟨75101,14,(.group 5 906 false)⟩)
(.leaf ⟨75115,14,(.group 5 907 false)⟩))))
(.branch 75185
(.branch 75157
(.branch 75143
(.leaf ⟨75129,14,(.group 5 908 false)⟩)
(.leaf ⟨75143,14,(.group 5 909 false)⟩))
(.branch 75171
(.leaf ⟨75157,14,(.group 5 910 false)⟩)
(.leaf ⟨75171,14,(.group 5 911 false)⟩)))
(.branch 75213
(.branch 75199
(.leaf ⟨75185,14,(.group 5 912 false)⟩)
(.leaf ⟨75199,14,(.group 5 913 false)⟩))
(.branch 75227
(.leaf ⟨75213,14,(.group 5 914 false)⟩)
(.leaf ⟨75227,14,(.group 5 915 false)⟩)))))
(.branch 75353
(.branch 75297
(.branch 75269
(.branch 75255
(.leaf ⟨75241,14,(.group 5 916 false)⟩)
(.leaf ⟨75255,14,(.group 5 917 false)⟩))
(.branch 75283
(.leaf ⟨75269,14,(.group 5 918 false)⟩)
(.leaf ⟨75283,14,(.group 5 919 false)⟩)))
(.branch 75325
(.branch 75311
(.leaf ⟨75297,14,(.group 5 920 false)⟩)
(.leaf ⟨75311,14,(.group 5 921 false)⟩))
(.branch 75339
(.leaf ⟨75325,14,(.group 5 922 false)⟩)
(.leaf ⟨75339,14,(.group 5 923 false)⟩))))
(.branch 75409
(.branch 75381
(.branch 75367
(.leaf ⟨75353,14,(.group 5 924 false)⟩)
(.leaf ⟨75367,14,(.group 5 925 false)⟩))
(.branch 75395
(.leaf ⟨75381,14,(.group 5 926 false)⟩)
(.leaf ⟨75395,14,(.group 5 927 false)⟩)))
(.branch 75437
(.branch 75423
(.leaf ⟨75409,14,(.group 5 928 false)⟩)
(.leaf ⟨75423,14,(.group 5 929 false)⟩))
(.branch 75451
(.leaf ⟨75437,14,(.group 5 930 false)⟩)
(.leaf ⟨75451,14,(.group 5 931 false)⟩))))))
(.branch 75689
(.branch 75577
(.branch 75521
(.branch 75493
(.branch 75479
(.leaf ⟨75465,14,(.group 5 932 false)⟩)
(.leaf ⟨75479,14,(.group 5 933 false)⟩))
(.branch 75507
(.leaf ⟨75493,14,(.group 5 934 false)⟩)
(.leaf ⟨75507,14,(.group 5 935 false)⟩)))
(.branch 75549
(.branch 75535
(.leaf ⟨75521,14,(.group 5 936 false)⟩)
(.leaf ⟨75535,14,(.group 5 937 false)⟩))
(.branch 75563
(.leaf ⟨75549,14,(.group 5 938 false)⟩)
(.leaf ⟨75563,14,(.group 5 939 false)⟩))))
(.branch 75633
(.branch 75605
(.branch 75591
(.leaf ⟨75577,14,(.group 5 940 false)⟩)
(.leaf ⟨75591,14,(.group 5 941 false)⟩))
(.branch 75619
(.leaf ⟨75605,14,(.group 5 942 false)⟩)
(.leaf ⟨75619,14,(.group 5 943 false)⟩)))
(.branch 75661
(.branch 75647
(.leaf ⟨75633,14,(.group 5 944 false)⟩)
(.leaf ⟨75647,14,(.group 5 945 false)⟩))
(.branch 75675
(.leaf ⟨75661,14,(.group 5 946 false)⟩)
(.leaf ⟨75675,14,(.group 5 947 false)⟩)))))
(.branch 75801
(.branch 75745
(.branch 75717
(.branch 75703
(.leaf ⟨75689,14,(.group 5 948 false)⟩)
(.leaf ⟨75703,14,(.group 5 949 false)⟩))
(.branch 75731
(.leaf ⟨75717,14,(.group 5 950 false)⟩)
(.leaf ⟨75731,14,(.group 5 951 false)⟩)))
(.branch 75773
(.branch 75759
(.leaf ⟨75745,14,(.group 5 952 false)⟩)
(.leaf ⟨75759,14,(.group 5 953 false)⟩))
(.branch 75787
(.leaf ⟨75773,14,(.group 5 954 false)⟩)
(.leaf ⟨75787,14,(.group 5 955 false)⟩))))
(.branch 75857
(.branch 75829
(.branch 75815
(.leaf ⟨75801,14,(.group 5 956 false)⟩)
(.leaf ⟨75815,14,(.group 5 957 false)⟩))
(.branch 75843
(.leaf ⟨75829,14,(.group 5 958 false)⟩)
(.leaf ⟨75843,14,(.group 5 959 false)⟩)))
(.branch 75885
(.branch 75871
(.leaf ⟨75857,14,(.group 5 960 false)⟩)
(.leaf ⟨75871,14,(.group 5 961 false)⟩))
(.branch 75899
(.leaf ⟨75885,14,(.group 5 962 false)⟩)
(.leaf ⟨75899,14,(.group 5 963 false)⟩)))))))

theorem tree77_checked : tree77.check 75017 75913 = true := by decide +kernel

def tree78 : Tree := (.branch 76361
(.branch 76137
(.branch 76025
(.branch 75969
(.branch 75941
(.branch 75927
(.leaf ⟨75913,14,(.group 5 964 false)⟩)
(.leaf ⟨75927,14,(.group 5 965 false)⟩))
(.branch 75955
(.leaf ⟨75941,14,(.group 5 966 false)⟩)
(.leaf ⟨75955,14,(.group 5 967 false)⟩)))
(.branch 75997
(.branch 75983
(.leaf ⟨75969,14,(.group 5 968 false)⟩)
(.leaf ⟨75983,14,(.group 5 969 false)⟩))
(.branch 76011
(.leaf ⟨75997,14,(.group 5 970 false)⟩)
(.leaf ⟨76011,14,(.group 5 971 false)⟩))))
(.branch 76081
(.branch 76053
(.branch 76039
(.leaf ⟨76025,14,(.group 5 972 false)⟩)
(.leaf ⟨76039,14,(.group 5 973 false)⟩))
(.branch 76067
(.leaf ⟨76053,14,(.group 5 974 false)⟩)
(.leaf ⟨76067,14,(.group 5 975 false)⟩)))
(.branch 76109
(.branch 76095
(.leaf ⟨76081,14,(.group 5 976 false)⟩)
(.leaf ⟨76095,14,(.group 5 977 false)⟩))
(.branch 76123
(.leaf ⟨76109,14,(.group 5 978 false)⟩)
(.leaf ⟨76123,14,(.group 5 979 false)⟩)))))
(.branch 76249
(.branch 76193
(.branch 76165
(.branch 76151
(.leaf ⟨76137,14,(.group 5 980 false)⟩)
(.leaf ⟨76151,14,(.group 5 981 false)⟩))
(.branch 76179
(.leaf ⟨76165,14,(.group 5 982 false)⟩)
(.leaf ⟨76179,14,(.group 5 983 false)⟩)))
(.branch 76221
(.branch 76207
(.leaf ⟨76193,14,(.group 5 984 false)⟩)
(.leaf ⟨76207,14,(.group 5 985 false)⟩))
(.branch 76235
(.leaf ⟨76221,14,(.group 5 986 false)⟩)
(.leaf ⟨76235,14,(.group 5 987 false)⟩))))
(.branch 76305
(.branch 76277
(.branch 76263
(.leaf ⟨76249,14,(.group 5 988 false)⟩)
(.leaf ⟨76263,14,(.group 5 989 false)⟩))
(.branch 76291
(.leaf ⟨76277,14,(.group 5 990 false)⟩)
(.leaf ⟨76291,14,(.group 5 991 false)⟩)))
(.branch 76333
(.branch 76319
(.leaf ⟨76305,14,(.group 5 992 false)⟩)
(.leaf ⟨76319,14,(.group 5 993 false)⟩))
(.branch 76347
(.leaf ⟨76333,14,(.group 5 994 false)⟩)
(.leaf ⟨76347,14,(.group 6 309 false)⟩))))))
(.branch 76585
(.branch 76473
(.branch 76417
(.branch 76389
(.branch 76375
(.leaf ⟨76361,14,(.group 6 310 false)⟩)
(.leaf ⟨76375,14,(.group 6 311 false)⟩))
(.branch 76403
(.leaf ⟨76389,14,(.group 6 312 false)⟩)
(.leaf ⟨76403,14,(.group 6 313 false)⟩)))
(.branch 76445
(.branch 76431
(.leaf ⟨76417,14,(.group 6 314 false)⟩)
(.leaf ⟨76431,14,(.group 6 315 false)⟩))
(.branch 76459
(.leaf ⟨76445,14,(.group 6 316 false)⟩)
(.leaf ⟨76459,14,(.group 6 317 false)⟩))))
(.branch 76529
(.branch 76501
(.branch 76487
(.leaf ⟨76473,14,(.group 6 318 false)⟩)
(.leaf ⟨76487,14,(.group 6 319 false)⟩))
(.branch 76515
(.leaf ⟨76501,14,(.group 6 320 false)⟩)
(.leaf ⟨76515,14,(.group 6 321 false)⟩)))
(.branch 76557
(.branch 76543
(.leaf ⟨76529,14,(.group 6 322 false)⟩)
(.leaf ⟨76543,14,(.group 6 323 false)⟩))
(.branch 76571
(.leaf ⟨76557,14,(.group 6 324 false)⟩)
(.leaf ⟨76571,14,(.group 6 325 false)⟩)))))
(.branch 76697
(.branch 76641
(.branch 76613
(.branch 76599
(.leaf ⟨76585,14,(.group 6 326 false)⟩)
(.leaf ⟨76599,14,(.group 6 327 false)⟩))
(.branch 76627
(.leaf ⟨76613,14,(.group 6 328 false)⟩)
(.leaf ⟨76627,14,(.group 6 329 false)⟩)))
(.branch 76669
(.branch 76655
(.leaf ⟨76641,14,(.group 6 330 false)⟩)
(.leaf ⟨76655,14,(.group 6 331 false)⟩))
(.branch 76683
(.leaf ⟨76669,14,(.group 6 332 false)⟩)
(.leaf ⟨76683,14,(.group 6 333 false)⟩))))
(.branch 76753
(.branch 76725
(.branch 76711
(.leaf ⟨76697,14,(.group 6 334 false)⟩)
(.leaf ⟨76711,14,(.group 6 335 false)⟩))
(.branch 76739
(.leaf ⟨76725,14,(.group 6 336 false)⟩)
(.leaf ⟨76739,14,(.group 6 337 false)⟩)))
(.branch 76781
(.branch 76767
(.leaf ⟨76753,14,(.group 6 338 false)⟩)
(.leaf ⟨76767,14,(.group 6 339 false)⟩))
(.branch 76795
(.leaf ⟨76781,14,(.group 6 340 false)⟩)
(.leaf ⟨76795,14,(.group 6 341 false)⟩)))))))

theorem tree78_checked : tree78.check 75913 76809 = true := by decide +kernel

def tree79 : Tree := (.branch 77257
(.branch 77033
(.branch 76921
(.branch 76865
(.branch 76837
(.branch 76823
(.leaf ⟨76809,14,(.group 6 342 false)⟩)
(.leaf ⟨76823,14,(.group 6 343 false)⟩))
(.branch 76851
(.leaf ⟨76837,14,(.group 6 344 false)⟩)
(.leaf ⟨76851,14,(.group 6 345 false)⟩)))
(.branch 76893
(.branch 76879
(.leaf ⟨76865,14,(.group 6 346 false)⟩)
(.leaf ⟨76879,14,(.group 6 347 false)⟩))
(.branch 76907
(.leaf ⟨76893,14,(.group 6 348 false)⟩)
(.leaf ⟨76907,14,(.group 6 349 false)⟩))))
(.branch 76977
(.branch 76949
(.branch 76935
(.leaf ⟨76921,14,(.group 6 350 false)⟩)
(.leaf ⟨76935,14,(.group 6 351 false)⟩))
(.branch 76963
(.leaf ⟨76949,14,(.group 6 352 false)⟩)
(.leaf ⟨76963,14,(.group 6 353 false)⟩)))
(.branch 77005
(.branch 76991
(.leaf ⟨76977,14,(.group 6 354 false)⟩)
(.leaf ⟨76991,14,(.group 6 355 false)⟩))
(.branch 77019
(.leaf ⟨77005,14,(.group 6 356 false)⟩)
(.leaf ⟨77019,14,(.group 6 357 false)⟩)))))
(.branch 77145
(.branch 77089
(.branch 77061
(.branch 77047
(.leaf ⟨77033,14,(.group 6 358 false)⟩)
(.leaf ⟨77047,14,(.group 6 359 false)⟩))
(.branch 77075
(.leaf ⟨77061,14,(.group 6 360 false)⟩)
(.leaf ⟨77075,14,(.group 6 361 false)⟩)))
(.branch 77117
(.branch 77103
(.leaf ⟨77089,14,(.group 6 362 false)⟩)
(.leaf ⟨77103,14,(.group 6 363 false)⟩))
(.branch 77131
(.leaf ⟨77117,14,(.group 6 364 false)⟩)
(.leaf ⟨77131,14,(.group 6 365 false)⟩))))
(.branch 77201
(.branch 77173
(.branch 77159
(.leaf ⟨77145,14,(.group 6 366 false)⟩)
(.leaf ⟨77159,14,(.group 6 367 false)⟩))
(.branch 77187
(.leaf ⟨77173,14,(.group 6 368 false)⟩)
(.leaf ⟨77187,14,(.group 6 369 false)⟩)))
(.branch 77229
(.branch 77215
(.leaf ⟨77201,14,(.group 6 370 false)⟩)
(.leaf ⟨77215,14,(.group 6 371 false)⟩))
(.branch 77243
(.leaf ⟨77229,14,(.group 6 372 false)⟩)
(.leaf ⟨77243,14,(.group 6 373 false)⟩))))))
(.branch 77481
(.branch 77369
(.branch 77313
(.branch 77285
(.branch 77271
(.leaf ⟨77257,14,(.group 6 374 false)⟩)
(.leaf ⟨77271,14,(.group 6 375 false)⟩))
(.branch 77299
(.leaf ⟨77285,14,(.group 6 376 false)⟩)
(.leaf ⟨77299,14,(.group 6 377 false)⟩)))
(.branch 77341
(.branch 77327
(.leaf ⟨77313,14,(.group 6 378 false)⟩)
(.leaf ⟨77327,14,(.group 6 379 false)⟩))
(.branch 77355
(.leaf ⟨77341,14,(.group 6 380 false)⟩)
(.leaf ⟨77355,14,(.group 6 381 false)⟩))))
(.branch 77425
(.branch 77397
(.branch 77383
(.leaf ⟨77369,14,(.group 6 382 false)⟩)
(.leaf ⟨77383,14,(.group 6 383 false)⟩))
(.branch 77411
(.leaf ⟨77397,14,(.group 6 384 false)⟩)
(.leaf ⟨77411,14,(.group 6 385 false)⟩)))
(.branch 77453
(.branch 77439
(.leaf ⟨77425,14,(.group 6 386 false)⟩)
(.leaf ⟨77439,14,(.group 6 387 false)⟩))
(.branch 77467
(.leaf ⟨77453,14,(.group 6 388 false)⟩)
(.leaf ⟨77467,14,(.group 6 389 false)⟩)))))
(.branch 77593
(.branch 77537
(.branch 77509
(.branch 77495
(.leaf ⟨77481,14,(.group 6 390 false)⟩)
(.leaf ⟨77495,14,(.group 6 391 false)⟩))
(.branch 77523
(.leaf ⟨77509,14,(.group 6 392 false)⟩)
(.leaf ⟨77523,14,(.group 6 393 false)⟩)))
(.branch 77565
(.branch 77551
(.leaf ⟨77537,14,(.group 6 394 false)⟩)
(.leaf ⟨77551,14,(.group 6 395 false)⟩))
(.branch 77579
(.leaf ⟨77565,14,(.group 6 396 false)⟩)
(.leaf ⟨77579,14,(.group 6 397 false)⟩))))
(.branch 77649
(.branch 77621
(.branch 77607
(.leaf ⟨77593,14,(.group 6 398 false)⟩)
(.leaf ⟨77607,14,(.group 6 399 false)⟩))
(.branch 77635
(.leaf ⟨77621,14,(.group 6 400 false)⟩)
(.leaf ⟨77635,14,(.group 6 401 false)⟩)))
(.branch 77677
(.branch 77663
(.leaf ⟨77649,14,(.group 6 402 false)⟩)
(.leaf ⟨77663,14,(.group 6 403 false)⟩))
(.branch 77691
(.leaf ⟨77677,14,(.group 6 404 false)⟩)
(.leaf ⟨77691,14,(.group 6 405 false)⟩)))))))

theorem tree79_checked : tree79.check 76809 77705 = true := by decide +kernel

def tree80 : Tree := (.branch 78153
(.branch 77929
(.branch 77817
(.branch 77761
(.branch 77733
(.branch 77719
(.leaf ⟨77705,14,(.group 6 406 false)⟩)
(.leaf ⟨77719,14,(.group 6 407 false)⟩))
(.branch 77747
(.leaf ⟨77733,14,(.group 6 408 false)⟩)
(.leaf ⟨77747,14,(.group 6 409 false)⟩)))
(.branch 77789
(.branch 77775
(.leaf ⟨77761,14,(.group 6 410 false)⟩)
(.leaf ⟨77775,14,(.group 6 411 false)⟩))
(.branch 77803
(.leaf ⟨77789,14,(.group 6 412 false)⟩)
(.leaf ⟨77803,14,(.group 6 413 false)⟩))))
(.branch 77873
(.branch 77845
(.branch 77831
(.leaf ⟨77817,14,(.group 6 414 false)⟩)
(.leaf ⟨77831,14,(.group 6 415 false)⟩))
(.branch 77859
(.leaf ⟨77845,14,(.group 6 416 false)⟩)
(.leaf ⟨77859,14,(.group 6 417 false)⟩)))
(.branch 77901
(.branch 77887
(.leaf ⟨77873,14,(.group 6 418 false)⟩)
(.leaf ⟨77887,14,(.group 6 419 false)⟩))
(.branch 77915
(.leaf ⟨77901,14,(.group 6 420 false)⟩)
(.leaf ⟨77915,14,(.group 6 421 false)⟩)))))
(.branch 78041
(.branch 77985
(.branch 77957
(.branch 77943
(.leaf ⟨77929,14,(.group 6 422 false)⟩)
(.leaf ⟨77943,14,(.group 6 423 false)⟩))
(.branch 77971
(.leaf ⟨77957,14,(.group 6 424 false)⟩)
(.leaf ⟨77971,14,(.group 6 425 false)⟩)))
(.branch 78013
(.branch 77999
(.leaf ⟨77985,14,(.group 6 426 false)⟩)
(.leaf ⟨77999,14,(.group 6 427 false)⟩))
(.branch 78027
(.leaf ⟨78013,14,(.group 6 428 false)⟩)
(.leaf ⟨78027,14,(.group 6 429 false)⟩))))
(.branch 78097
(.branch 78069
(.branch 78055
(.leaf ⟨78041,14,(.group 6 430 false)⟩)
(.leaf ⟨78055,14,(.group 6 431 false)⟩))
(.branch 78083
(.leaf ⟨78069,14,(.group 6 432 false)⟩)
(.leaf ⟨78083,14,(.group 6 433 false)⟩)))
(.branch 78125
(.branch 78111
(.leaf ⟨78097,14,(.group 6 434 false)⟩)
(.leaf ⟨78111,14,(.group 6 435 false)⟩))
(.branch 78139
(.leaf ⟨78125,14,(.group 6 436 false)⟩)
(.leaf ⟨78139,14,(.group 6 437 false)⟩))))))
(.branch 78377
(.branch 78265
(.branch 78209
(.branch 78181
(.branch 78167
(.leaf ⟨78153,14,(.group 6 438 false)⟩)
(.leaf ⟨78167,14,(.group 6 439 false)⟩))
(.branch 78195
(.leaf ⟨78181,14,(.group 6 440 false)⟩)
(.leaf ⟨78195,14,(.group 6 441 false)⟩)))
(.branch 78237
(.branch 78223
(.leaf ⟨78209,14,(.group 6 442 false)⟩)
(.leaf ⟨78223,14,(.group 6 443 false)⟩))
(.branch 78251
(.leaf ⟨78237,14,(.group 6 444 false)⟩)
(.leaf ⟨78251,14,(.group 6 445 false)⟩))))
(.branch 78321
(.branch 78293
(.branch 78279
(.leaf ⟨78265,14,(.group 6 446 false)⟩)
(.leaf ⟨78279,14,(.group 6 447 false)⟩))
(.branch 78307
(.leaf ⟨78293,14,(.group 6 448 false)⟩)
(.leaf ⟨78307,14,(.group 6 449 false)⟩)))
(.branch 78349
(.branch 78335
(.leaf ⟨78321,14,(.group 6 450 false)⟩)
(.leaf ⟨78335,14,(.group 6 451 false)⟩))
(.branch 78363
(.leaf ⟨78349,14,(.group 6 452 false)⟩)
(.leaf ⟨78363,14,(.group 6 453 false)⟩)))))
(.branch 78489
(.branch 78433
(.branch 78405
(.branch 78391
(.leaf ⟨78377,14,(.group 6 454 false)⟩)
(.leaf ⟨78391,14,(.group 6 455 false)⟩))
(.branch 78419
(.leaf ⟨78405,14,(.group 6 456 false)⟩)
(.leaf ⟨78419,14,(.group 6 457 false)⟩)))
(.branch 78461
(.branch 78447
(.leaf ⟨78433,14,(.group 6 458 false)⟩)
(.leaf ⟨78447,14,(.group 6 459 false)⟩))
(.branch 78475
(.leaf ⟨78461,14,(.group 6 460 false)⟩)
(.leaf ⟨78475,14,(.group 6 461 false)⟩))))
(.branch 78545
(.branch 78517
(.branch 78503
(.leaf ⟨78489,14,(.group 6 462 false)⟩)
(.leaf ⟨78503,14,(.group 6 463 false)⟩))
(.branch 78531
(.leaf ⟨78517,14,(.group 6 464 false)⟩)
(.leaf ⟨78531,14,(.group 7 112 false)⟩)))
(.branch 78573
(.branch 78559
(.leaf ⟨78545,14,(.group 7 113 false)⟩)
(.leaf ⟨78559,14,(.group 7 114 false)⟩))
(.branch 78587
(.leaf ⟨78573,14,(.group 7 115 false)⟩)
(.leaf ⟨78587,14,(.group 7 116 false)⟩)))))))

theorem tree80_checked : tree80.check 77705 78601 = true := by decide +kernel

def tree81 : Tree := (.branch 79049
(.branch 78825
(.branch 78713
(.branch 78657
(.branch 78629
(.branch 78615
(.leaf ⟨78601,14,(.group 7 117 false)⟩)
(.leaf ⟨78615,14,(.group 7 118 false)⟩))
(.branch 78643
(.leaf ⟨78629,14,(.group 7 119 false)⟩)
(.leaf ⟨78643,14,(.group 7 120 false)⟩)))
(.branch 78685
(.branch 78671
(.leaf ⟨78657,14,(.group 7 121 false)⟩)
(.leaf ⟨78671,14,(.group 7 122 false)⟩))
(.branch 78699
(.leaf ⟨78685,14,(.group 7 123 false)⟩)
(.leaf ⟨78699,14,(.group 7 124 false)⟩))))
(.branch 78769
(.branch 78741
(.branch 78727
(.leaf ⟨78713,14,(.group 7 125 false)⟩)
(.leaf ⟨78727,14,(.group 7 126 false)⟩))
(.branch 78755
(.leaf ⟨78741,14,(.group 7 127 false)⟩)
(.leaf ⟨78755,14,(.group 7 128 false)⟩)))
(.branch 78797
(.branch 78783
(.leaf ⟨78769,14,(.group 7 129 false)⟩)
(.leaf ⟨78783,14,(.group 7 130 false)⟩))
(.branch 78811
(.leaf ⟨78797,14,(.group 7 131 false)⟩)
(.leaf ⟨78811,14,(.group 7 132 false)⟩)))))
(.branch 78937
(.branch 78881
(.branch 78853
(.branch 78839
(.leaf ⟨78825,14,(.group 7 133 false)⟩)
(.leaf ⟨78839,14,(.group 7 134 false)⟩))
(.branch 78867
(.leaf ⟨78853,14,(.group 7 135 false)⟩)
(.leaf ⟨78867,14,(.group 7 136 false)⟩)))
(.branch 78909
(.branch 78895
(.leaf ⟨78881,14,(.group 7 137 false)⟩)
(.leaf ⟨78895,14,(.group 7 138 false)⟩))
(.branch 78923
(.leaf ⟨78909,14,(.group 7 139 false)⟩)
(.leaf ⟨78923,14,(.group 7 140 false)⟩))))
(.branch 78993
(.branch 78965
(.branch 78951
(.leaf ⟨78937,14,(.group 7 141 false)⟩)
(.leaf ⟨78951,14,(.group 7 142 false)⟩))
(.branch 78979
(.leaf ⟨78965,14,(.group 7 143 false)⟩)
(.leaf ⟨78979,14,(.group 7 144 false)⟩)))
(.branch 79021
(.branch 79007
(.leaf ⟨78993,14,(.group 7 145 false)⟩)
(.leaf ⟨79007,14,(.group 7 146 false)⟩))
(.branch 79035
(.leaf ⟨79021,14,(.group 7 147 false)⟩)
(.leaf ⟨79035,14,(.group 7 148 false)⟩))))))
(.branch 79273
(.branch 79161
(.branch 79105
(.branch 79077
(.branch 79063
(.leaf ⟨79049,14,(.group 7 149 false)⟩)
(.leaf ⟨79063,14,(.group 8 160 false)⟩))
(.branch 79091
(.leaf ⟨79077,14,(.group 8 161 false)⟩)
(.leaf ⟨79091,14,(.group 8 162 false)⟩)))
(.branch 79133
(.branch 79119
(.leaf ⟨79105,14,(.group 8 163 false)⟩)
(.leaf ⟨79119,14,(.group 8 164 false)⟩))
(.branch 79147
(.leaf ⟨79133,14,(.group 8 165 false)⟩)
(.leaf ⟨79147,14,(.group 8 166 false)⟩))))
(.branch 79217
(.branch 79189
(.branch 79175
(.leaf ⟨79161,14,(.group 8 167 false)⟩)
(.leaf ⟨79175,14,(.group 8 168 false)⟩))
(.branch 79203
(.leaf ⟨79189,14,(.group 8 169 false)⟩)
(.leaf ⟨79203,14,(.group 8 170 false)⟩)))
(.branch 79245
(.branch 79231
(.leaf ⟨79217,14,(.group 8 171 false)⟩)
(.leaf ⟨79231,14,(.group 8 172 false)⟩))
(.branch 79259
(.leaf ⟨79245,14,(.group 8 173 false)⟩)
(.leaf ⟨79259,14,(.group 8 174 false)⟩)))))
(.branch 79385
(.branch 79329
(.branch 79301
(.branch 79287
(.leaf ⟨79273,14,(.group 8 175 false)⟩)
(.leaf ⟨79287,14,(.group 8 176 false)⟩))
(.branch 79315
(.leaf ⟨79301,14,(.group 8 177 false)⟩)
(.leaf ⟨79315,14,(.group 8 178 false)⟩)))
(.branch 79357
(.branch 79343
(.leaf ⟨79329,14,(.group 8 179 false)⟩)
(.leaf ⟨79343,14,(.group 8 180 false)⟩))
(.branch 79371
(.leaf ⟨79357,14,(.group 8 181 false)⟩)
(.leaf ⟨79371,14,(.group 8 182 false)⟩))))
(.branch 79441
(.branch 79413
(.branch 79399
(.leaf ⟨79385,14,(.group 8 183 false)⟩)
(.leaf ⟨79399,14,(.group 8 184 false)⟩))
(.branch 79427
(.leaf ⟨79413,14,(.group 8 185 false)⟩)
(.leaf ⟨79427,14,(.group 8 186 false)⟩)))
(.branch 79469
(.branch 79455
(.leaf ⟨79441,14,(.group 8 187 false)⟩)
(.leaf ⟨79455,14,(.group 8 188 false)⟩))
(.branch 79483
(.leaf ⟨79469,14,(.group 8 189 false)⟩)
(.leaf ⟨79483,14,(.group 8 190 false)⟩)))))))

theorem tree81_checked : tree81.check 78601 79497 = true := by decide +kernel

def tree82 : Tree := (.branch 79945
(.branch 79721
(.branch 79609
(.branch 79553
(.branch 79525
(.branch 79511
(.leaf ⟨79497,14,(.group 8 191 false)⟩)
(.leaf ⟨79511,14,(.group 8 192 false)⟩))
(.branch 79539
(.leaf ⟨79525,14,(.group 8 193 false)⟩)
(.leaf ⟨79539,14,(.group 8 194 false)⟩)))
(.branch 79581
(.branch 79567
(.leaf ⟨79553,14,(.group 8 195 false)⟩)
(.leaf ⟨79567,14,(.group 8 196 false)⟩))
(.branch 79595
(.leaf ⟨79581,14,(.group 8 197 false)⟩)
(.leaf ⟨79595,14,(.group 8 198 false)⟩))))
(.branch 79665
(.branch 79637
(.branch 79623
(.leaf ⟨79609,14,(.group 8 199 false)⟩)
(.leaf ⟨79623,14,(.group 8 200 false)⟩))
(.branch 79651
(.leaf ⟨79637,14,(.group 8 201 false)⟩)
(.leaf ⟨79651,14,(.group 9 158 false)⟩)))
(.branch 79693
(.branch 79679
(.leaf ⟨79665,14,(.group 9 159 false)⟩)
(.leaf ⟨79679,14,(.group 9 160 false)⟩))
(.branch 79707
(.leaf ⟨79693,14,(.group 9 161 false)⟩)
(.leaf ⟨79707,14,(.group 9 162 false)⟩)))))
(.branch 79833
(.branch 79777
(.branch 79749
(.branch 79735
(.leaf ⟨79721,14,(.group 9 163 false)⟩)
(.leaf ⟨79735,14,(.group 9 164 false)⟩))
(.branch 79763
(.leaf ⟨79749,14,(.group 9 165 false)⟩)
(.leaf ⟨79763,14,(.group 9 166 false)⟩)))
(.branch 79805
(.branch 79791
(.leaf ⟨79777,14,(.group 9 167 false)⟩)
(.leaf ⟨79791,14,(.group 9 168 false)⟩))
(.branch 79819
(.leaf ⟨79805,14,(.group 9 169 false)⟩)
(.leaf ⟨79819,14,(.group 9 170 false)⟩))))
(.branch 79889
(.branch 79861
(.branch 79847
(.leaf ⟨79833,14,(.group 9 171 false)⟩)
(.leaf ⟨79847,14,(.group 9 172 false)⟩))
(.branch 79875
(.leaf ⟨79861,14,(.group 9 173 false)⟩)
(.leaf ⟨79875,14,(.group 9 174 false)⟩)))
(.branch 79917
(.branch 79903
(.leaf ⟨79889,14,(.group 9 175 false)⟩)
(.leaf ⟨79903,14,(.group 9 176 false)⟩))
(.branch 79931
(.leaf ⟨79917,14,(.group 9 177 false)⟩)
(.leaf ⟨79931,14,(.group 9 178 false)⟩))))))
(.branch 80173
(.branch 80057
(.branch 80001
(.branch 79973
(.branch 79959
(.leaf ⟨79945,14,(.group 9 179 false)⟩)
(.leaf ⟨79959,14,(.group 9 180 false)⟩))
(.branch 79987
(.leaf ⟨79973,14,(.group 9 181 false)⟩)
(.leaf ⟨79987,14,(.group 9 182 false)⟩)))
(.branch 80029
(.branch 80015
(.leaf ⟨80001,14,(.group 9 183 false)⟩)
(.leaf ⟨80015,14,(.group 9 184 false)⟩))
(.branch 80043
(.leaf ⟨80029,14,(.group 9 185 false)⟩)
(.leaf ⟨80043,14,(.group 9 186 false)⟩))))
(.branch 80113
(.branch 80085
(.branch 80071
(.leaf ⟨80057,14,(.group 9 187 false)⟩)
(.leaf ⟨80071,14,(.group 9 188 false)⟩))
(.branch 80099
(.leaf ⟨80085,14,(.group 9 189 false)⟩)
(.leaf ⟨80099,14,(.group 9 190 false)⟩)))
(.branch 80143
(.branch 80128
(.leaf ⟨80113,15,(.group 0 328 false)⟩)
(.leaf ⟨80128,15,(.group 0 329 false)⟩))
(.branch 80158
(.leaf ⟨80143,15,(.group 0 330 false)⟩)
(.leaf ⟨80158,15,(.group 0 331 false)⟩)))))
(.branch 80293
(.branch 80233
(.branch 80203
(.branch 80188
(.leaf ⟨80173,15,(.group 0 332 false)⟩)
(.leaf ⟨80188,15,(.group 0 333 false)⟩))
(.branch 80218
(.leaf ⟨80203,15,(.group 0 334 false)⟩)
(.leaf ⟨80218,15,(.group 0 335 false)⟩)))
(.branch 80263
(.branch 80248
(.leaf ⟨80233,15,(.group 0 336 false)⟩)
(.leaf ⟨80248,15,(.group 0 337 false)⟩))
(.branch 80278
(.leaf ⟨80263,15,(.group 0 338 false)⟩)
(.leaf ⟨80278,15,(.group 0 339 false)⟩))))
(.branch 80353
(.branch 80323
(.branch 80308
(.leaf ⟨80293,15,(.group 0 340 false)⟩)
(.leaf ⟨80308,15,(.group 0 341 false)⟩))
(.branch 80338
(.leaf ⟨80323,15,(.group 0 342 false)⟩)
(.leaf ⟨80338,15,(.group 0 343 false)⟩)))
(.branch 80383
(.branch 80368
(.leaf ⟨80353,15,(.group 0 344 false)⟩)
(.leaf ⟨80368,15,(.group 0 345 false)⟩))
(.branch 80398
(.leaf ⟨80383,15,(.group 0 346 false)⟩)
(.leaf ⟨80398,15,(.group 0 347 false)⟩)))))))

theorem tree82_checked : tree82.check 79497 80413 = true := by decide +kernel

def tree83 : Tree := (.branch 80893
(.branch 80653
(.branch 80533
(.branch 80473
(.branch 80443
(.branch 80428
(.leaf ⟨80413,15,(.group 0 348 false)⟩)
(.leaf ⟨80428,15,(.group 0 349 false)⟩))
(.branch 80458
(.leaf ⟨80443,15,(.group 0 350 false)⟩)
(.leaf ⟨80458,15,(.group 0 351 false)⟩)))
(.branch 80503
(.branch 80488
(.leaf ⟨80473,15,(.group 0 352 false)⟩)
(.leaf ⟨80488,15,(.group 0 353 false)⟩))
(.branch 80518
(.leaf ⟨80503,15,(.group 0 354 false)⟩)
(.leaf ⟨80518,15,(.group 0 355 false)⟩))))
(.branch 80593
(.branch 80563
(.branch 80548
(.leaf ⟨80533,15,(.group 0 356 false)⟩)
(.leaf ⟨80548,15,(.group 0 357 false)⟩))
(.branch 80578
(.leaf ⟨80563,15,(.group 0 358 false)⟩)
(.leaf ⟨80578,15,(.group 0 359 false)⟩)))
(.branch 80623
(.branch 80608
(.leaf ⟨80593,15,(.group 0 360 false)⟩)
(.leaf ⟨80608,15,(.group 0 361 false)⟩))
(.branch 80638
(.leaf ⟨80623,15,(.group 0 362 false)⟩)
(.leaf ⟨80638,15,(.group 0 363 false)⟩)))))
(.branch 80773
(.branch 80713
(.branch 80683
(.branch 80668
(.leaf ⟨80653,15,(.group 0 364 false)⟩)
(.leaf ⟨80668,15,(.group 0 365 false)⟩))
(.branch 80698
(.leaf ⟨80683,15,(.group 0 366 false)⟩)
(.leaf ⟨80698,15,(.group 0 367 false)⟩)))
(.branch 80743
(.branch 80728
(.leaf ⟨80713,15,(.group 0 368 false)⟩)
(.leaf ⟨80728,15,(.group 0 369 false)⟩))
(.branch 80758
(.leaf ⟨80743,15,(.group 0 370 false)⟩)
(.leaf ⟨80758,15,(.group 0 371 false)⟩))))
(.branch 80833
(.branch 80803
(.branch 80788
(.leaf ⟨80773,15,(.group 0 372 false)⟩)
(.leaf ⟨80788,15,(.group 0 373 false)⟩))
(.branch 80818
(.leaf ⟨80803,15,(.group 0 374 false)⟩)
(.leaf ⟨80818,15,(.group 0 375 false)⟩)))
(.branch 80863
(.branch 80848
(.leaf ⟨80833,15,(.group 0 376 false)⟩)
(.leaf ⟨80848,15,(.group 0 377 false)⟩))
(.branch 80878
(.leaf ⟨80863,15,(.group 0 378 false)⟩)
(.leaf ⟨80878,15,(.group 0 379 false)⟩))))))
(.branch 81133
(.branch 81013
(.branch 80953
(.branch 80923
(.branch 80908
(.leaf ⟨80893,15,(.group 0 380 false)⟩)
(.leaf ⟨80908,15,(.group 0 381 false)⟩))
(.branch 80938
(.leaf ⟨80923,15,(.group 0 382 false)⟩)
(.leaf ⟨80938,15,(.group 0 383 false)⟩)))
(.branch 80983
(.branch 80968
(.leaf ⟨80953,15,(.group 0 384 false)⟩)
(.leaf ⟨80968,15,(.group 0 385 false)⟩))
(.branch 80998
(.leaf ⟨80983,15,(.group 0 386 false)⟩)
(.leaf ⟨80998,15,(.group 0 387 false)⟩))))
(.branch 81073
(.branch 81043
(.branch 81028
(.leaf ⟨81013,15,(.group 0 388 false)⟩)
(.leaf ⟨81028,15,(.group 0 389 false)⟩))
(.branch 81058
(.leaf ⟨81043,15,(.group 0 390 false)⟩)
(.leaf ⟨81058,15,(.group 0 391 false)⟩)))
(.branch 81103
(.branch 81088
(.leaf ⟨81073,15,(.group 0 392 false)⟩)
(.leaf ⟨81088,15,(.group 0 393 false)⟩))
(.branch 81118
(.leaf ⟨81103,15,(.group 0 394 false)⟩)
(.leaf ⟨81118,15,(.group 0 395 false)⟩)))))
(.branch 81253
(.branch 81193
(.branch 81163
(.branch 81148
(.leaf ⟨81133,15,(.group 0 396 false)⟩)
(.leaf ⟨81148,15,(.group 0 397 false)⟩))
(.branch 81178
(.leaf ⟨81163,15,(.group 0 398 false)⟩)
(.leaf ⟨81178,15,(.group 0 399 false)⟩)))
(.branch 81223
(.branch 81208
(.leaf ⟨81193,15,(.group 0 400 false)⟩)
(.leaf ⟨81208,15,(.group 0 401 false)⟩))
(.branch 81238
(.leaf ⟨81223,15,(.group 0 402 false)⟩)
(.leaf ⟨81238,15,(.group 0 403 false)⟩))))
(.branch 81313
(.branch 81283
(.branch 81268
(.leaf ⟨81253,15,(.group 0 404 false)⟩)
(.leaf ⟨81268,15,(.group 0 405 false)⟩))
(.branch 81298
(.leaf ⟨81283,15,(.group 0 406 false)⟩)
(.leaf ⟨81298,15,(.group 0 407 false)⟩)))
(.branch 81343
(.branch 81328
(.leaf ⟨81313,15,(.group 0 408 false)⟩)
(.leaf ⟨81328,15,(.group 0 409 false)⟩))
(.branch 81358
(.leaf ⟨81343,15,(.group 0 410 false)⟩)
(.leaf ⟨81358,15,(.group 0 411 false)⟩)))))))

theorem tree83_checked : tree83.check 80413 81373 = true := by decide +kernel

def tree84 : Tree := (.branch 81853
(.branch 81613
(.branch 81493
(.branch 81433
(.branch 81403
(.branch 81388
(.leaf ⟨81373,15,(.group 0 412 false)⟩)
(.leaf ⟨81388,15,(.group 0 413 false)⟩))
(.branch 81418
(.leaf ⟨81403,15,(.group 0 414 false)⟩)
(.leaf ⟨81418,15,(.group 0 415 false)⟩)))
(.branch 81463
(.branch 81448
(.leaf ⟨81433,15,(.group 0 416 false)⟩)
(.leaf ⟨81448,15,(.group 0 417 false)⟩))
(.branch 81478
(.leaf ⟨81463,15,(.group 0 418 false)⟩)
(.leaf ⟨81478,15,(.group 0 419 false)⟩))))
(.branch 81553
(.branch 81523
(.branch 81508
(.leaf ⟨81493,15,(.group 0 420 false)⟩)
(.leaf ⟨81508,15,(.group 0 421 false)⟩))
(.branch 81538
(.leaf ⟨81523,15,(.group 0 422 false)⟩)
(.leaf ⟨81538,15,(.group 0 423 false)⟩)))
(.branch 81583
(.branch 81568
(.leaf ⟨81553,15,(.group 0 424 false)⟩)
(.leaf ⟨81568,15,(.group 0 425 false)⟩))
(.branch 81598
(.leaf ⟨81583,15,(.group 0 426 false)⟩)
(.leaf ⟨81598,15,(.group 0 427 false)⟩)))))
(.branch 81733
(.branch 81673
(.branch 81643
(.branch 81628
(.leaf ⟨81613,15,(.group 0 428 false)⟩)
(.leaf ⟨81628,15,(.group 0 429 false)⟩))
(.branch 81658
(.leaf ⟨81643,15,(.group 0 430 false)⟩)
(.leaf ⟨81658,15,(.group 0 431 false)⟩)))
(.branch 81703
(.branch 81688
(.leaf ⟨81673,15,(.group 0 432 false)⟩)
(.leaf ⟨81688,15,(.group 0 433 false)⟩))
(.branch 81718
(.leaf ⟨81703,15,(.group 0 434 false)⟩)
(.leaf ⟨81718,15,(.group 0 435 false)⟩))))
(.branch 81793
(.branch 81763
(.branch 81748
(.leaf ⟨81733,15,(.group 0 436 false)⟩)
(.leaf ⟨81748,15,(.group 0 437 false)⟩))
(.branch 81778
(.leaf ⟨81763,15,(.group 1 120 false)⟩)
(.leaf ⟨81778,15,(.group 1 121 false)⟩)))
(.branch 81823
(.branch 81808
(.leaf ⟨81793,15,(.group 1 122 false)⟩)
(.leaf ⟨81808,15,(.group 1 123 false)⟩))
(.branch 81838
(.leaf ⟨81823,15,(.group 1 124 false)⟩)
(.leaf ⟨81838,15,(.group 1 125 false)⟩))))))
(.branch 82093
(.branch 81973
(.branch 81913
(.branch 81883
(.branch 81868
(.leaf ⟨81853,15,(.group 1 126 false)⟩)
(.leaf ⟨81868,15,(.group 1 127 false)⟩))
(.branch 81898
(.leaf ⟨81883,15,(.group 1 128 false)⟩)
(.leaf ⟨81898,15,(.group 1 129 false)⟩)))
(.branch 81943
(.branch 81928
(.leaf ⟨81913,15,(.group 1 130 false)⟩)
(.leaf ⟨81928,15,(.group 1 131 false)⟩))
(.branch 81958
(.leaf ⟨81943,15,(.group 1 132 false)⟩)
(.leaf ⟨81958,15,(.group 1 133 false)⟩))))
(.branch 82033
(.branch 82003
(.branch 81988
(.leaf ⟨81973,15,(.group 1 134 false)⟩)
(.leaf ⟨81988,15,(.group 1 135 false)⟩))
(.branch 82018
(.leaf ⟨82003,15,(.group 1 136 false)⟩)
(.leaf ⟨82018,15,(.group 1 137 false)⟩)))
(.branch 82063
(.branch 82048
(.leaf ⟨82033,15,(.group 1 138 false)⟩)
(.leaf ⟨82048,15,(.group 1 139 false)⟩))
(.branch 82078
(.leaf ⟨82063,15,(.group 1 140 false)⟩)
(.leaf ⟨82078,15,(.group 1 141 false)⟩)))))
(.branch 82213
(.branch 82153
(.branch 82123
(.branch 82108
(.leaf ⟨82093,15,(.group 1 142 false)⟩)
(.leaf ⟨82108,15,(.group 1 143 false)⟩))
(.branch 82138
(.leaf ⟨82123,15,(.group 1 144 false)⟩)
(.leaf ⟨82138,15,(.group 1 145 false)⟩)))
(.branch 82183
(.branch 82168
(.leaf ⟨82153,15,(.group 1 146 false)⟩)
(.leaf ⟨82168,15,(.group 1 147 false)⟩))
(.branch 82198
(.leaf ⟨82183,15,(.group 1 148 false)⟩)
(.leaf ⟨82198,15,(.group 1 149 false)⟩))))
(.branch 82273
(.branch 82243
(.branch 82228
(.leaf ⟨82213,15,(.group 1 150 false)⟩)
(.leaf ⟨82228,15,(.group 1 151 false)⟩))
(.branch 82258
(.leaf ⟨82243,15,(.group 1 152 false)⟩)
(.leaf ⟨82258,15,(.group 1 153 false)⟩)))
(.branch 82303
(.branch 82288
(.leaf ⟨82273,15,(.group 1 154 false)⟩)
(.leaf ⟨82288,15,(.group 1 155 false)⟩))
(.branch 82318
(.leaf ⟨82303,15,(.group 1 156 false)⟩)
(.leaf ⟨82318,15,(.group 1 157 false)⟩)))))))

theorem tree84_checked : tree84.check 81373 82333 = true := by decide +kernel

def tree85 : Tree := (.branch 82813
(.branch 82573
(.branch 82453
(.branch 82393
(.branch 82363
(.branch 82348
(.leaf ⟨82333,15,(.group 1 158 false)⟩)
(.leaf ⟨82348,15,(.group 1 159 false)⟩))
(.branch 82378
(.leaf ⟨82363,15,(.group 1 160 false)⟩)
(.leaf ⟨82378,15,(.group 1 161 false)⟩)))
(.branch 82423
(.branch 82408
(.leaf ⟨82393,15,(.group 1 162 false)⟩)
(.leaf ⟨82408,15,(.group 1 163 false)⟩))
(.branch 82438
(.leaf ⟨82423,15,(.group 1 164 false)⟩)
(.leaf ⟨82438,15,(.group 2 120 false)⟩))))
(.branch 82513
(.branch 82483
(.branch 82468
(.leaf ⟨82453,15,(.group 2 121 false)⟩)
(.leaf ⟨82468,15,(.group 2 122 false)⟩))
(.branch 82498
(.leaf ⟨82483,15,(.group 2 123 false)⟩)
(.leaf ⟨82498,15,(.group 2 124 false)⟩)))
(.branch 82543
(.branch 82528
(.leaf ⟨82513,15,(.group 2 125 false)⟩)
(.leaf ⟨82528,15,(.group 2 126 false)⟩))
(.branch 82558
(.leaf ⟨82543,15,(.group 2 127 false)⟩)
(.leaf ⟨82558,15,(.group 2 128 false)⟩)))))
(.branch 82693
(.branch 82633
(.branch 82603
(.branch 82588
(.leaf ⟨82573,15,(.group 2 129 false)⟩)
(.leaf ⟨82588,15,(.group 2 130 false)⟩))
(.branch 82618
(.leaf ⟨82603,15,(.group 2 131 false)⟩)
(.leaf ⟨82618,15,(.group 2 132 false)⟩)))
(.branch 82663
(.branch 82648
(.leaf ⟨82633,15,(.group 2 133 false)⟩)
(.leaf ⟨82648,15,(.group 2 134 false)⟩))
(.branch 82678
(.leaf ⟨82663,15,(.group 2 135 false)⟩)
(.leaf ⟨82678,15,(.group 2 136 false)⟩))))
(.branch 82753
(.branch 82723
(.branch 82708
(.leaf ⟨82693,15,(.group 2 137 false)⟩)
(.leaf ⟨82708,15,(.group 2 138 false)⟩))
(.branch 82738
(.leaf ⟨82723,15,(.group 2 139 false)⟩)
(.leaf ⟨82738,15,(.group 2 140 false)⟩)))
(.branch 82783
(.branch 82768
(.leaf ⟨82753,15,(.group 2 141 false)⟩)
(.leaf ⟨82768,15,(.group 2 142 false)⟩))
(.branch 82798
(.leaf ⟨82783,15,(.group 2 143 false)⟩)
(.leaf ⟨82798,15,(.group 2 144 false)⟩))))))
(.branch 83053
(.branch 82933
(.branch 82873
(.branch 82843
(.branch 82828
(.leaf ⟨82813,15,(.group 2 145 false)⟩)
(.leaf ⟨82828,15,(.group 2 146 false)⟩))
(.branch 82858
(.leaf ⟨82843,15,(.group 2 147 false)⟩)
(.leaf ⟨82858,15,(.group 2 148 false)⟩)))
(.branch 82903
(.branch 82888
(.leaf ⟨82873,15,(.group 2 149 false)⟩)
(.leaf ⟨82888,15,(.group 2 150 false)⟩))
(.branch 82918
(.leaf ⟨82903,15,(.group 2 151 false)⟩)
(.leaf ⟨82918,15,(.group 2 152 false)⟩))))
(.branch 82993
(.branch 82963
(.branch 82948
(.leaf ⟨82933,15,(.group 2 153 false)⟩)
(.leaf ⟨82948,15,(.group 2 154 false)⟩))
(.branch 82978
(.leaf ⟨82963,15,(.group 2 155 false)⟩)
(.leaf ⟨82978,15,(.group 2 156 false)⟩)))
(.branch 83023
(.branch 83008
(.leaf ⟨82993,15,(.group 2 157 false)⟩)
(.leaf ⟨83008,15,(.group 2 158 false)⟩))
(.branch 83038
(.leaf ⟨83023,15,(.group 2 159 false)⟩)
(.leaf ⟨83038,15,(.group 2 160 false)⟩)))))
(.branch 83173
(.branch 83113
(.branch 83083
(.branch 83068
(.leaf ⟨83053,15,(.group 2 161 false)⟩)
(.leaf ⟨83068,15,(.group 2 162 false)⟩))
(.branch 83098
(.leaf ⟨83083,15,(.group 2 163 false)⟩)
(.leaf ⟨83098,15,(.group 2 164 false)⟩)))
(.branch 83143
(.branch 83128
(.leaf ⟨83113,15,(.group 3 120 false)⟩)
(.leaf ⟨83128,15,(.group 3 121 false)⟩))
(.branch 83158
(.leaf ⟨83143,15,(.group 3 122 false)⟩)
(.leaf ⟨83158,15,(.group 3 123 false)⟩))))
(.branch 83233
(.branch 83203
(.branch 83188
(.leaf ⟨83173,15,(.group 3 124 false)⟩)
(.leaf ⟨83188,15,(.group 3 125 false)⟩))
(.branch 83218
(.leaf ⟨83203,15,(.group 3 126 false)⟩)
(.leaf ⟨83218,15,(.group 3 127 false)⟩)))
(.branch 83263
(.branch 83248
(.leaf ⟨83233,15,(.group 3 128 false)⟩)
(.leaf ⟨83248,15,(.group 3 129 false)⟩))
(.branch 83278
(.leaf ⟨83263,15,(.group 3 130 false)⟩)
(.leaf ⟨83278,15,(.group 3 131 false)⟩)))))))

theorem tree85_checked : tree85.check 82333 83293 = true := by decide +kernel

def tree86 : Tree := (.branch 83773
(.branch 83533
(.branch 83413
(.branch 83353
(.branch 83323
(.branch 83308
(.leaf ⟨83293,15,(.group 3 132 false)⟩)
(.leaf ⟨83308,15,(.group 3 133 false)⟩))
(.branch 83338
(.leaf ⟨83323,15,(.group 3 134 false)⟩)
(.leaf ⟨83338,15,(.group 3 135 false)⟩)))
(.branch 83383
(.branch 83368
(.leaf ⟨83353,15,(.group 3 136 false)⟩)
(.leaf ⟨83368,15,(.group 3 137 false)⟩))
(.branch 83398
(.leaf ⟨83383,15,(.group 3 138 false)⟩)
(.leaf ⟨83398,15,(.group 3 139 false)⟩))))
(.branch 83473
(.branch 83443
(.branch 83428
(.leaf ⟨83413,15,(.group 3 140 false)⟩)
(.leaf ⟨83428,15,(.group 3 141 false)⟩))
(.branch 83458
(.leaf ⟨83443,15,(.group 3 142 false)⟩)
(.leaf ⟨83458,15,(.group 3 143 false)⟩)))
(.branch 83503
(.branch 83488
(.leaf ⟨83473,15,(.group 3 144 false)⟩)
(.leaf ⟨83488,15,(.group 3 145 false)⟩))
(.branch 83518
(.leaf ⟨83503,15,(.group 3 146 false)⟩)
(.leaf ⟨83518,15,(.group 3 147 false)⟩)))))
(.branch 83653
(.branch 83593
(.branch 83563
(.branch 83548
(.leaf ⟨83533,15,(.group 3 148 false)⟩)
(.leaf ⟨83548,15,(.group 3 149 false)⟩))
(.branch 83578
(.leaf ⟨83563,15,(.group 3 150 false)⟩)
(.leaf ⟨83578,15,(.group 3 151 false)⟩)))
(.branch 83623
(.branch 83608
(.leaf ⟨83593,15,(.group 3 152 false)⟩)
(.leaf ⟨83608,15,(.group 3 153 false)⟩))
(.branch 83638
(.leaf ⟨83623,15,(.group 3 154 false)⟩)
(.leaf ⟨83638,15,(.group 3 155 false)⟩))))
(.branch 83713
(.branch 83683
(.branch 83668
(.leaf ⟨83653,15,(.group 3 156 false)⟩)
(.leaf ⟨83668,15,(.group 3 157 false)⟩))
(.branch 83698
(.leaf ⟨83683,15,(.group 3 158 false)⟩)
(.leaf ⟨83698,15,(.group 3 159 false)⟩)))
(.branch 83743
(.branch 83728
(.leaf ⟨83713,15,(.group 3 160 false)⟩)
(.leaf ⟨83728,15,(.group 3 161 false)⟩))
(.branch 83758
(.leaf ⟨83743,15,(.group 3 162 false)⟩)
(.leaf ⟨83758,15,(.group 3 163 false)⟩))))))
(.branch 84013
(.branch 83893
(.branch 83833
(.branch 83803
(.branch 83788
(.leaf ⟨83773,15,(.group 3 164 false)⟩)
(.leaf ⟨83788,15,(.group 4 120 false)⟩))
(.branch 83818
(.leaf ⟨83803,15,(.group 4 121 false)⟩)
(.leaf ⟨83818,15,(.group 4 122 false)⟩)))
(.branch 83863
(.branch 83848
(.leaf ⟨83833,15,(.group 4 123 false)⟩)
(.leaf ⟨83848,15,(.group 4 124 false)⟩))
(.branch 83878
(.leaf ⟨83863,15,(.group 4 125 false)⟩)
(.leaf ⟨83878,15,(.group 4 126 false)⟩))))
(.branch 83953
(.branch 83923
(.branch 83908
(.leaf ⟨83893,15,(.group 4 127 false)⟩)
(.leaf ⟨83908,15,(.group 4 128 false)⟩))
(.branch 83938
(.leaf ⟨83923,15,(.group 4 129 false)⟩)
(.leaf ⟨83938,15,(.group 4 130 false)⟩)))
(.branch 83983
(.branch 83968
(.leaf ⟨83953,15,(.group 4 131 false)⟩)
(.leaf ⟨83968,15,(.group 4 132 false)⟩))
(.branch 83998
(.leaf ⟨83983,15,(.group 4 133 false)⟩)
(.leaf ⟨83998,15,(.group 4 134 false)⟩)))))
(.branch 84133
(.branch 84073
(.branch 84043
(.branch 84028
(.leaf ⟨84013,15,(.group 4 135 false)⟩)
(.leaf ⟨84028,15,(.group 4 136 false)⟩))
(.branch 84058
(.leaf ⟨84043,15,(.group 4 137 false)⟩)
(.leaf ⟨84058,15,(.group 4 138 false)⟩)))
(.branch 84103
(.branch 84088
(.leaf ⟨84073,15,(.group 4 139 false)⟩)
(.leaf ⟨84088,15,(.group 4 140 false)⟩))
(.branch 84118
(.leaf ⟨84103,15,(.group 4 141 false)⟩)
(.leaf ⟨84118,15,(.group 4 142 false)⟩))))
(.branch 84193
(.branch 84163
(.branch 84148
(.leaf ⟨84133,15,(.group 4 143 false)⟩)
(.leaf ⟨84148,15,(.group 4 144 false)⟩))
(.branch 84178
(.leaf ⟨84163,15,(.group 4 145 false)⟩)
(.leaf ⟨84178,15,(.group 4 146 false)⟩)))
(.branch 84223
(.branch 84208
(.leaf ⟨84193,15,(.group 4 147 false)⟩)
(.leaf ⟨84208,15,(.group 4 148 false)⟩))
(.branch 84238
(.leaf ⟨84223,15,(.group 4 149 false)⟩)
(.leaf ⟨84238,15,(.group 4 150 false)⟩)))))))

theorem tree86_checked : tree86.check 83293 84253 = true := by decide +kernel

def tree87 : Tree := (.branch 84733
(.branch 84493
(.branch 84373
(.branch 84313
(.branch 84283
(.branch 84268
(.leaf ⟨84253,15,(.group 4 151 false)⟩)
(.leaf ⟨84268,15,(.group 4 152 false)⟩))
(.branch 84298
(.leaf ⟨84283,15,(.group 4 153 false)⟩)
(.leaf ⟨84298,15,(.group 4 154 false)⟩)))
(.branch 84343
(.branch 84328
(.leaf ⟨84313,15,(.group 4 155 false)⟩)
(.leaf ⟨84328,15,(.group 4 156 false)⟩))
(.branch 84358
(.leaf ⟨84343,15,(.group 4 157 false)⟩)
(.leaf ⟨84358,15,(.group 4 158 false)⟩))))
(.branch 84433
(.branch 84403
(.branch 84388
(.leaf ⟨84373,15,(.group 4 159 false)⟩)
(.leaf ⟨84388,15,(.group 4 160 false)⟩))
(.branch 84418
(.leaf ⟨84403,15,(.group 4 161 false)⟩)
(.leaf ⟨84418,15,(.group 4 162 false)⟩)))
(.branch 84463
(.branch 84448
(.leaf ⟨84433,15,(.group 4 163 false)⟩)
(.leaf ⟨84448,15,(.group 4 164 false)⟩))
(.branch 84478
(.leaf ⟨84463,15,(.group 5 995 false)⟩)
(.leaf ⟨84478,15,(.group 5 996 false)⟩)))))
(.branch 84613
(.branch 84553
(.branch 84523
(.branch 84508
(.leaf ⟨84493,15,(.group 5 997 false)⟩)
(.leaf ⟨84508,15,(.group 5 998 false)⟩))
(.branch 84538
(.leaf ⟨84523,15,(.group 5 999 false)⟩)
(.leaf ⟨84538,15,(.group 5 1000 false)⟩)))
(.branch 84583
(.branch 84568
(.leaf ⟨84553,15,(.group 5 1001 false)⟩)
(.leaf ⟨84568,15,(.group 5 1002 false)⟩))
(.branch 84598
(.leaf ⟨84583,15,(.group 5 1003 false)⟩)
(.leaf ⟨84598,15,(.group 5 1004 false)⟩))))
(.branch 84673
(.branch 84643
(.branch 84628
(.leaf ⟨84613,15,(.group 5 1005 false)⟩)
(.leaf ⟨84628,15,(.group 5 1006 false)⟩))
(.branch 84658
(.leaf ⟨84643,15,(.group 5 1007 false)⟩)
(.leaf ⟨84658,15,(.group 5 1008 false)⟩)))
(.branch 84703
(.branch 84688
(.leaf ⟨84673,15,(.group 5 1009 false)⟩)
(.leaf ⟨84688,15,(.group 5 1010 false)⟩))
(.branch 84718
(.leaf ⟨84703,15,(.group 5 1011 false)⟩)
(.leaf ⟨84718,15,(.group 5 1012 false)⟩))))))
(.branch 84973
(.branch 84853
(.branch 84793
(.branch 84763
(.branch 84748
(.leaf ⟨84733,15,(.group 5 1013 false)⟩)
(.leaf ⟨84748,15,(.group 5 1014 false)⟩))
(.branch 84778
(.leaf ⟨84763,15,(.group 5 1015 false)⟩)
(.leaf ⟨84778,15,(.group 5 1016 false)⟩)))
(.branch 84823
(.branch 84808
(.leaf ⟨84793,15,(.group 5 1017 false)⟩)
(.leaf ⟨84808,15,(.group 5 1018 false)⟩))
(.branch 84838
(.leaf ⟨84823,15,(.group 5 1019 false)⟩)
(.leaf ⟨84838,15,(.group 5 1020 false)⟩))))
(.branch 84913
(.branch 84883
(.branch 84868
(.leaf ⟨84853,15,(.group 5 1021 false)⟩)
(.leaf ⟨84868,15,(.group 5 1022 false)⟩))
(.branch 84898
(.leaf ⟨84883,15,(.group 5 1023 false)⟩)
(.leaf ⟨84898,15,(.group 5 1024 false)⟩)))
(.branch 84943
(.branch 84928
(.leaf ⟨84913,15,(.group 5 1025 false)⟩)
(.leaf ⟨84928,15,(.group 5 1026 false)⟩))
(.branch 84958
(.leaf ⟨84943,15,(.group 5 1027 false)⟩)
(.leaf ⟨84958,15,(.group 5 1028 false)⟩)))))
(.branch 85093
(.branch 85033
(.branch 85003
(.branch 84988
(.leaf ⟨84973,15,(.group 5 1029 false)⟩)
(.leaf ⟨84988,15,(.group 5 1030 false)⟩))
(.branch 85018
(.leaf ⟨85003,15,(.group 5 1031 false)⟩)
(.leaf ⟨85018,15,(.group 5 1032 false)⟩)))
(.branch 85063
(.branch 85048
(.leaf ⟨85033,15,(.group 5 1033 false)⟩)
(.leaf ⟨85048,15,(.group 5 1034 false)⟩))
(.branch 85078
(.leaf ⟨85063,15,(.group 5 1035 false)⟩)
(.leaf ⟨85078,15,(.group 5 1036 false)⟩))))
(.branch 85153
(.branch 85123
(.branch 85108
(.leaf ⟨85093,15,(.group 5 1037 false)⟩)
(.leaf ⟨85108,15,(.group 5 1038 false)⟩))
(.branch 85138
(.leaf ⟨85123,15,(.group 5 1039 false)⟩)
(.leaf ⟨85138,15,(.group 5 1040 false)⟩)))
(.branch 85183
(.branch 85168
(.leaf ⟨85153,15,(.group 5 1041 false)⟩)
(.leaf ⟨85168,15,(.group 5 1042 false)⟩))
(.branch 85198
(.leaf ⟨85183,15,(.group 5 1043 false)⟩)
(.leaf ⟨85198,15,(.group 5 1044 false)⟩)))))))

theorem tree87_checked : tree87.check 84253 85213 = true := by decide +kernel

def tree88 : Tree := (.branch 85693
(.branch 85453
(.branch 85333
(.branch 85273
(.branch 85243
(.branch 85228
(.leaf ⟨85213,15,(.group 5 1045 false)⟩)
(.leaf ⟨85228,15,(.group 5 1046 false)⟩))
(.branch 85258
(.leaf ⟨85243,15,(.group 5 1047 false)⟩)
(.leaf ⟨85258,15,(.group 5 1048 false)⟩)))
(.branch 85303
(.branch 85288
(.leaf ⟨85273,15,(.group 5 1049 false)⟩)
(.leaf ⟨85288,15,(.group 5 1050 false)⟩))
(.branch 85318
(.leaf ⟨85303,15,(.group 5 1051 false)⟩)
(.leaf ⟨85318,15,(.group 5 1052 false)⟩))))
(.branch 85393
(.branch 85363
(.branch 85348
(.leaf ⟨85333,15,(.group 5 1053 false)⟩)
(.leaf ⟨85348,15,(.group 5 1054 false)⟩))
(.branch 85378
(.leaf ⟨85363,15,(.group 5 1055 false)⟩)
(.leaf ⟨85378,15,(.group 5 1056 false)⟩)))
(.branch 85423
(.branch 85408
(.leaf ⟨85393,15,(.group 5 1057 false)⟩)
(.leaf ⟨85408,15,(.group 5 1058 false)⟩))
(.branch 85438
(.leaf ⟨85423,15,(.group 5 1059 false)⟩)
(.leaf ⟨85438,15,(.group 5 1060 false)⟩)))))
(.branch 85573
(.branch 85513
(.branch 85483
(.branch 85468
(.leaf ⟨85453,15,(.group 5 1061 false)⟩)
(.leaf ⟨85468,15,(.group 5 1062 false)⟩))
(.branch 85498
(.leaf ⟨85483,15,(.group 5 1063 false)⟩)
(.leaf ⟨85498,15,(.group 5 1064 false)⟩)))
(.branch 85543
(.branch 85528
(.leaf ⟨85513,15,(.group 5 1065 false)⟩)
(.leaf ⟨85528,15,(.group 5 1066 false)⟩))
(.branch 85558
(.leaf ⟨85543,15,(.group 5 1067 false)⟩)
(.leaf ⟨85558,15,(.group 5 1068 false)⟩))))
(.branch 85633
(.branch 85603
(.branch 85588
(.leaf ⟨85573,15,(.group 5 1069 false)⟩)
(.leaf ⟨85588,15,(.group 5 1070 false)⟩))
(.branch 85618
(.leaf ⟨85603,15,(.group 5 1071 false)⟩)
(.leaf ⟨85618,15,(.group 5 1072 false)⟩)))
(.branch 85663
(.branch 85648
(.leaf ⟨85633,15,(.group 5 1073 false)⟩)
(.leaf ⟨85648,15,(.group 5 1074 false)⟩))
(.branch 85678
(.leaf ⟨85663,15,(.group 5 1075 false)⟩)
(.leaf ⟨85678,15,(.group 5 1076 false)⟩))))))
(.branch 85933
(.branch 85813
(.branch 85753
(.branch 85723
(.branch 85708
(.leaf ⟨85693,15,(.group 5 1077 false)⟩)
(.leaf ⟨85708,15,(.group 5 1078 false)⟩))
(.branch 85738
(.leaf ⟨85723,15,(.group 5 1079 false)⟩)
(.leaf ⟨85738,15,(.group 5 1080 false)⟩)))
(.branch 85783
(.branch 85768
(.leaf ⟨85753,15,(.group 5 1081 false)⟩)
(.leaf ⟨85768,15,(.group 5 1082 false)⟩))
(.branch 85798
(.leaf ⟨85783,15,(.group 5 1083 false)⟩)
(.leaf ⟨85798,15,(.group 5 1084 false)⟩))))
(.branch 85873
(.branch 85843
(.branch 85828
(.leaf ⟨85813,15,(.group 5 1085 false)⟩)
(.leaf ⟨85828,15,(.group 5 1086 false)⟩))
(.branch 85858
(.leaf ⟨85843,15,(.group 5 1087 false)⟩)
(.leaf ⟨85858,15,(.group 5 1088 false)⟩)))
(.branch 85903
(.branch 85888
(.leaf ⟨85873,15,(.group 5 1089 false)⟩)
(.leaf ⟨85888,15,(.group 5 1090 false)⟩))
(.branch 85918
(.leaf ⟨85903,15,(.group 5 1091 false)⟩)
(.leaf ⟨85918,15,(.group 5 1092 false)⟩)))))
(.branch 86053
(.branch 85993
(.branch 85963
(.branch 85948
(.leaf ⟨85933,15,(.group 5 1093 false)⟩)
(.leaf ⟨85948,15,(.group 5 1094 false)⟩))
(.branch 85978
(.leaf ⟨85963,15,(.group 5 1095 false)⟩)
(.leaf ⟨85978,15,(.group 5 1096 false)⟩)))
(.branch 86023
(.branch 86008
(.leaf ⟨85993,15,(.group 5 1097 false)⟩)
(.leaf ⟨86008,15,(.group 5 1098 false)⟩))
(.branch 86038
(.leaf ⟨86023,15,(.group 5 1099 false)⟩)
(.leaf ⟨86038,15,(.group 5 1100 false)⟩))))
(.branch 86113
(.branch 86083
(.branch 86068
(.leaf ⟨86053,15,(.group 5 1101 false)⟩)
(.leaf ⟨86068,15,(.group 5 1102 false)⟩))
(.branch 86098
(.leaf ⟨86083,15,(.group 5 1103 false)⟩)
(.leaf ⟨86098,15,(.group 5 1104 false)⟩)))
(.branch 86143
(.branch 86128
(.leaf ⟨86113,15,(.group 5 1105 false)⟩)
(.leaf ⟨86128,15,(.group 5 1106 false)⟩))
(.branch 86158
(.leaf ⟨86143,15,(.group 5 1107 false)⟩)
(.leaf ⟨86158,15,(.group 5 1108 false)⟩)))))))

theorem tree88_checked : tree88.check 85213 86173 = true := by decide +kernel

def tree89 : Tree := (.branch 86653
(.branch 86413
(.branch 86293
(.branch 86233
(.branch 86203
(.branch 86188
(.leaf ⟨86173,15,(.group 5 1109 false)⟩)
(.leaf ⟨86188,15,(.group 5 1110 false)⟩))
(.branch 86218
(.leaf ⟨86203,15,(.group 5 1111 false)⟩)
(.leaf ⟨86218,15,(.group 5 1112 false)⟩)))
(.branch 86263
(.branch 86248
(.leaf ⟨86233,15,(.group 5 1113 false)⟩)
(.leaf ⟨86248,15,(.group 5 1114 false)⟩))
(.branch 86278
(.leaf ⟨86263,15,(.group 5 1115 false)⟩)
(.leaf ⟨86278,15,(.group 5 1116 false)⟩))))
(.branch 86353
(.branch 86323
(.branch 86308
(.leaf ⟨86293,15,(.group 5 1117 false)⟩)
(.leaf ⟨86308,15,(.group 5 1118 false)⟩))
(.branch 86338
(.leaf ⟨86323,15,(.group 5 1119 false)⟩)
(.leaf ⟨86338,15,(.group 5 1120 false)⟩)))
(.branch 86383
(.branch 86368
(.leaf ⟨86353,15,(.group 5 1121 false)⟩)
(.leaf ⟨86368,15,(.group 5 1122 false)⟩))
(.branch 86398
(.leaf ⟨86383,15,(.group 5 1123 false)⟩)
(.leaf ⟨86398,15,(.group 5 1124 false)⟩)))))
(.branch 86533
(.branch 86473
(.branch 86443
(.branch 86428
(.leaf ⟨86413,15,(.group 5 1125 false)⟩)
(.leaf ⟨86428,15,(.group 5 1126 false)⟩))
(.branch 86458
(.leaf ⟨86443,15,(.group 5 1127 false)⟩)
(.leaf ⟨86458,15,(.group 5 1128 false)⟩)))
(.branch 86503
(.branch 86488
(.leaf ⟨86473,15,(.group 5 1129 false)⟩)
(.leaf ⟨86488,15,(.group 5 1130 false)⟩))
(.branch 86518
(.leaf ⟨86503,15,(.group 5 1131 false)⟩)
(.leaf ⟨86518,15,(.group 5 1132 false)⟩))))
(.branch 86593
(.branch 86563
(.branch 86548
(.leaf ⟨86533,15,(.group 5 1133 false)⟩)
(.leaf ⟨86548,15,(.group 5 1134 false)⟩))
(.branch 86578
(.leaf ⟨86563,15,(.group 5 1135 false)⟩)
(.leaf ⟨86578,15,(.group 5 1136 false)⟩)))
(.branch 86623
(.branch 86608
(.leaf ⟨86593,15,(.group 5 1137 false)⟩)
(.leaf ⟨86608,15,(.group 5 1138 false)⟩))
(.branch 86638
(.leaf ⟨86623,15,(.group 5 1139 false)⟩)
(.leaf ⟨86638,15,(.group 5 1140 false)⟩))))))
(.branch 86893
(.branch 86773
(.branch 86713
(.branch 86683
(.branch 86668
(.leaf ⟨86653,15,(.group 5 1141 false)⟩)
(.leaf ⟨86668,15,(.group 5 1142 false)⟩))
(.branch 86698
(.leaf ⟨86683,15,(.group 5 1143 false)⟩)
(.leaf ⟨86698,15,(.group 5 1144 false)⟩)))
(.branch 86743
(.branch 86728
(.leaf ⟨86713,15,(.group 5 1145 false)⟩)
(.leaf ⟨86728,15,(.group 5 1146 false)⟩))
(.branch 86758
(.leaf ⟨86743,15,(.group 5 1147 false)⟩)
(.leaf ⟨86758,15,(.group 5 1148 false)⟩))))
(.branch 86833
(.branch 86803
(.branch 86788
(.leaf ⟨86773,15,(.group 5 1149 false)⟩)
(.leaf ⟨86788,15,(.group 5 1150 false)⟩))
(.branch 86818
(.leaf ⟨86803,15,(.group 5 1151 false)⟩)
(.leaf ⟨86818,15,(.group 5 1152 false)⟩)))
(.branch 86863
(.branch 86848
(.leaf ⟨86833,15,(.group 5 1153 false)⟩)
(.leaf ⟨86848,15,(.group 5 1154 false)⟩))
(.branch 86878
(.leaf ⟨86863,15,(.group 5 1155 false)⟩)
(.leaf ⟨86878,15,(.group 5 1156 false)⟩)))))
(.branch 87013
(.branch 86953
(.branch 86923
(.branch 86908
(.leaf ⟨86893,15,(.group 5 1157 false)⟩)
(.leaf ⟨86908,15,(.group 5 1158 false)⟩))
(.branch 86938
(.leaf ⟨86923,15,(.group 5 1159 false)⟩)
(.leaf ⟨86938,15,(.group 5 1160 false)⟩)))
(.branch 86983
(.branch 86968
(.leaf ⟨86953,15,(.group 5 1161 false)⟩)
(.leaf ⟨86968,15,(.group 5 1162 false)⟩))
(.branch 86998
(.leaf ⟨86983,15,(.group 5 1163 false)⟩)
(.leaf ⟨86998,15,(.group 5 1164 false)⟩))))
(.branch 87073
(.branch 87043
(.branch 87028
(.leaf ⟨87013,15,(.group 5 1165 false)⟩)
(.leaf ⟨87028,15,(.group 5 1166 false)⟩))
(.branch 87058
(.leaf ⟨87043,15,(.group 5 1167 false)⟩)
(.leaf ⟨87058,15,(.group 5 1168 false)⟩)))
(.branch 87103
(.branch 87088
(.leaf ⟨87073,15,(.group 5 1169 false)⟩)
(.leaf ⟨87088,15,(.group 5 1170 false)⟩))
(.branch 87118
(.leaf ⟨87103,15,(.group 5 1171 false)⟩)
(.leaf ⟨87118,15,(.group 5 1172 false)⟩)))))))

theorem tree89_checked : tree89.check 86173 87133 = true := by decide +kernel

def tree90 : Tree := (.branch 87613
(.branch 87373
(.branch 87253
(.branch 87193
(.branch 87163
(.branch 87148
(.leaf ⟨87133,15,(.group 5 1173 false)⟩)
(.leaf ⟨87148,15,(.group 5 1174 false)⟩))
(.branch 87178
(.leaf ⟨87163,15,(.group 5 1175 false)⟩)
(.leaf ⟨87178,15,(.group 5 1176 false)⟩)))
(.branch 87223
(.branch 87208
(.leaf ⟨87193,15,(.group 5 1177 false)⟩)
(.leaf ⟨87208,15,(.group 5 1178 false)⟩))
(.branch 87238
(.leaf ⟨87223,15,(.group 5 1179 false)⟩)
(.leaf ⟨87238,15,(.group 5 1180 false)⟩))))
(.branch 87313
(.branch 87283
(.branch 87268
(.leaf ⟨87253,15,(.group 5 1181 false)⟩)
(.leaf ⟨87268,15,(.group 5 1182 false)⟩))
(.branch 87298
(.leaf ⟨87283,15,(.group 5 1183 false)⟩)
(.leaf ⟨87298,15,(.group 5 1184 false)⟩)))
(.branch 87343
(.branch 87328
(.leaf ⟨87313,15,(.group 5 1185 false)⟩)
(.leaf ⟨87328,15,(.group 5 1186 false)⟩))
(.branch 87358
(.leaf ⟨87343,15,(.group 5 1187 false)⟩)
(.leaf ⟨87358,15,(.group 5 1188 false)⟩)))))
(.branch 87493
(.branch 87433
(.branch 87403
(.branch 87388
(.leaf ⟨87373,15,(.group 5 1189 false)⟩)
(.leaf ⟨87388,15,(.group 5 1190 false)⟩))
(.branch 87418
(.leaf ⟨87403,15,(.group 5 1191 false)⟩)
(.leaf ⟨87418,15,(.group 5 1192 false)⟩)))
(.branch 87463
(.branch 87448
(.leaf ⟨87433,15,(.group 5 1193 false)⟩)
(.leaf ⟨87448,15,(.group 5 1194 false)⟩))
(.branch 87478
(.leaf ⟨87463,15,(.group 5 1195 false)⟩)
(.leaf ⟨87478,15,(.group 5 1196 false)⟩))))
(.branch 87553
(.branch 87523
(.branch 87508
(.leaf ⟨87493,15,(.group 5 1197 false)⟩)
(.leaf ⟨87508,15,(.group 5 1198 false)⟩))
(.branch 87538
(.leaf ⟨87523,15,(.group 5 1199 false)⟩)
(.leaf ⟨87538,15,(.group 5 1200 false)⟩)))
(.branch 87583
(.branch 87568
(.leaf ⟨87553,15,(.group 5 1201 false)⟩)
(.leaf ⟨87568,15,(.group 5 1202 false)⟩))
(.branch 87598
(.leaf ⟨87583,15,(.group 5 1203 false)⟩)
(.leaf ⟨87598,15,(.group 5 1204 false)⟩))))))
(.branch 87853
(.branch 87733
(.branch 87673
(.branch 87643
(.branch 87628
(.leaf ⟨87613,15,(.group 5 1205 false)⟩)
(.leaf ⟨87628,15,(.group 5 1206 false)⟩))
(.branch 87658
(.leaf ⟨87643,15,(.group 5 1207 false)⟩)
(.leaf ⟨87658,15,(.group 5 1208 false)⟩)))
(.branch 87703
(.branch 87688
(.leaf ⟨87673,15,(.group 5 1209 false)⟩)
(.leaf ⟨87688,15,(.group 5 1210 false)⟩))
(.branch 87718
(.leaf ⟨87703,15,(.group 5 1211 false)⟩)
(.leaf ⟨87718,15,(.group 5 1212 false)⟩))))
(.branch 87793
(.branch 87763
(.branch 87748
(.leaf ⟨87733,15,(.group 5 1213 false)⟩)
(.leaf ⟨87748,15,(.group 5 1214 false)⟩))
(.branch 87778
(.leaf ⟨87763,15,(.group 6 465 false)⟩)
(.leaf ⟨87778,15,(.group 6 466 false)⟩)))
(.branch 87823
(.branch 87808
(.leaf ⟨87793,15,(.group 6 467 false)⟩)
(.leaf ⟨87808,15,(.group 6 468 false)⟩))
(.branch 87838
(.leaf ⟨87823,15,(.group 6 469 false)⟩)
(.leaf ⟨87838,15,(.group 6 470 false)⟩)))))
(.branch 87973
(.branch 87913
(.branch 87883
(.branch 87868
(.leaf ⟨87853,15,(.group 6 471 false)⟩)
(.leaf ⟨87868,15,(.group 6 472 false)⟩))
(.branch 87898
(.leaf ⟨87883,15,(.group 6 473 false)⟩)
(.leaf ⟨87898,15,(.group 6 474 false)⟩)))
(.branch 87943
(.branch 87928
(.leaf ⟨87913,15,(.group 6 475 false)⟩)
(.leaf ⟨87928,15,(.group 6 476 false)⟩))
(.branch 87958
(.leaf ⟨87943,15,(.group 6 477 false)⟩)
(.leaf ⟨87958,15,(.group 6 478 false)⟩))))
(.branch 88033
(.branch 88003
(.branch 87988
(.leaf ⟨87973,15,(.group 6 479 false)⟩)
(.leaf ⟨87988,15,(.group 6 480 false)⟩))
(.branch 88018
(.leaf ⟨88003,15,(.group 6 481 false)⟩)
(.leaf ⟨88018,15,(.group 6 482 false)⟩)))
(.branch 88063
(.branch 88048
(.leaf ⟨88033,15,(.group 6 483 false)⟩)
(.leaf ⟨88048,15,(.group 6 484 false)⟩))
(.branch 88078
(.leaf ⟨88063,15,(.group 6 485 false)⟩)
(.leaf ⟨88078,15,(.group 6 486 false)⟩)))))))

theorem tree90_checked : tree90.check 87133 88093 = true := by decide +kernel

def tree91 : Tree := (.branch 88573
(.branch 88333
(.branch 88213
(.branch 88153
(.branch 88123
(.branch 88108
(.leaf ⟨88093,15,(.group 6 487 false)⟩)
(.leaf ⟨88108,15,(.group 6 488 false)⟩))
(.branch 88138
(.leaf ⟨88123,15,(.group 6 489 false)⟩)
(.leaf ⟨88138,15,(.group 6 490 false)⟩)))
(.branch 88183
(.branch 88168
(.leaf ⟨88153,15,(.group 6 491 false)⟩)
(.leaf ⟨88168,15,(.group 6 492 false)⟩))
(.branch 88198
(.leaf ⟨88183,15,(.group 6 493 false)⟩)
(.leaf ⟨88198,15,(.group 6 494 false)⟩))))
(.branch 88273
(.branch 88243
(.branch 88228
(.leaf ⟨88213,15,(.group 6 495 false)⟩)
(.leaf ⟨88228,15,(.group 6 496 false)⟩))
(.branch 88258
(.leaf ⟨88243,15,(.group 6 497 false)⟩)
(.leaf ⟨88258,15,(.group 6 498 false)⟩)))
(.branch 88303
(.branch 88288
(.leaf ⟨88273,15,(.group 6 499 false)⟩)
(.leaf ⟨88288,15,(.group 6 500 false)⟩))
(.branch 88318
(.leaf ⟨88303,15,(.group 6 501 false)⟩)
(.leaf ⟨88318,15,(.group 6 502 false)⟩)))))
(.branch 88453
(.branch 88393
(.branch 88363
(.branch 88348
(.leaf ⟨88333,15,(.group 6 503 false)⟩)
(.leaf ⟨88348,15,(.group 6 504 false)⟩))
(.branch 88378
(.leaf ⟨88363,15,(.group 6 505 false)⟩)
(.leaf ⟨88378,15,(.group 6 506 false)⟩)))
(.branch 88423
(.branch 88408
(.leaf ⟨88393,15,(.group 6 507 false)⟩)
(.leaf ⟨88408,15,(.group 6 508 false)⟩))
(.branch 88438
(.leaf ⟨88423,15,(.group 6 509 false)⟩)
(.leaf ⟨88438,15,(.group 6 510 false)⟩))))
(.branch 88513
(.branch 88483
(.branch 88468
(.leaf ⟨88453,15,(.group 6 511 false)⟩)
(.leaf ⟨88468,15,(.group 6 512 false)⟩))
(.branch 88498
(.leaf ⟨88483,15,(.group 6 513 false)⟩)
(.leaf ⟨88498,15,(.group 6 514 false)⟩)))
(.branch 88543
(.branch 88528
(.leaf ⟨88513,15,(.group 6 515 false)⟩)
(.leaf ⟨88528,15,(.group 6 516 false)⟩))
(.branch 88558
(.leaf ⟨88543,15,(.group 6 517 false)⟩)
(.leaf ⟨88558,15,(.group 6 518 false)⟩))))))
(.branch 88813
(.branch 88693
(.branch 88633
(.branch 88603
(.branch 88588
(.leaf ⟨88573,15,(.group 6 519 false)⟩)
(.leaf ⟨88588,15,(.group 6 520 false)⟩))
(.branch 88618
(.leaf ⟨88603,15,(.group 6 521 false)⟩)
(.leaf ⟨88618,15,(.group 6 522 false)⟩)))
(.branch 88663
(.branch 88648
(.leaf ⟨88633,15,(.group 6 523 false)⟩)
(.leaf ⟨88648,15,(.group 6 524 false)⟩))
(.branch 88678
(.leaf ⟨88663,15,(.group 6 525 false)⟩)
(.leaf ⟨88678,15,(.group 6 526 false)⟩))))
(.branch 88753
(.branch 88723
(.branch 88708
(.leaf ⟨88693,15,(.group 6 527 false)⟩)
(.leaf ⟨88708,15,(.group 6 528 false)⟩))
(.branch 88738
(.leaf ⟨88723,15,(.group 6 529 false)⟩)
(.leaf ⟨88738,15,(.group 6 530 false)⟩)))
(.branch 88783
(.branch 88768
(.leaf ⟨88753,15,(.group 6 531 false)⟩)
(.leaf ⟨88768,15,(.group 6 532 false)⟩))
(.branch 88798
(.leaf ⟨88783,15,(.group 6 533 false)⟩)
(.leaf ⟨88798,15,(.group 6 534 false)⟩)))))
(.branch 88933
(.branch 88873
(.branch 88843
(.branch 88828
(.leaf ⟨88813,15,(.group 6 535 false)⟩)
(.leaf ⟨88828,15,(.group 6 536 false)⟩))
(.branch 88858
(.leaf ⟨88843,15,(.group 6 537 false)⟩)
(.leaf ⟨88858,15,(.group 6 538 false)⟩)))
(.branch 88903
(.branch 88888
(.leaf ⟨88873,15,(.group 6 539 false)⟩)
(.leaf ⟨88888,15,(.group 6 540 false)⟩))
(.branch 88918
(.leaf ⟨88903,15,(.group 6 541 false)⟩)
(.leaf ⟨88918,15,(.group 6 542 false)⟩))))
(.branch 88993
(.branch 88963
(.branch 88948
(.leaf ⟨88933,15,(.group 6 543 false)⟩)
(.leaf ⟨88948,15,(.group 6 544 false)⟩))
(.branch 88978
(.leaf ⟨88963,15,(.group 6 545 false)⟩)
(.leaf ⟨88978,15,(.group 6 546 false)⟩)))
(.branch 89023
(.branch 89008
(.leaf ⟨88993,15,(.group 6 547 false)⟩)
(.leaf ⟨89008,15,(.group 6 548 false)⟩))
(.branch 89038
(.leaf ⟨89023,15,(.group 6 549 false)⟩)
(.leaf ⟨89038,15,(.group 6 550 false)⟩)))))))

theorem tree91_checked : tree91.check 88093 89053 = true := by decide +kernel

def tree92 : Tree := (.branch 89533
(.branch 89293
(.branch 89173
(.branch 89113
(.branch 89083
(.branch 89068
(.leaf ⟨89053,15,(.group 6 551 false)⟩)
(.leaf ⟨89068,15,(.group 6 552 false)⟩))
(.branch 89098
(.leaf ⟨89083,15,(.group 6 553 false)⟩)
(.leaf ⟨89098,15,(.group 6 554 false)⟩)))
(.branch 89143
(.branch 89128
(.leaf ⟨89113,15,(.group 6 555 false)⟩)
(.leaf ⟨89128,15,(.group 6 556 false)⟩))
(.branch 89158
(.leaf ⟨89143,15,(.group 6 557 false)⟩)
(.leaf ⟨89158,15,(.group 6 558 false)⟩))))
(.branch 89233
(.branch 89203
(.branch 89188
(.leaf ⟨89173,15,(.group 6 559 false)⟩)
(.leaf ⟨89188,15,(.group 6 560 false)⟩))
(.branch 89218
(.leaf ⟨89203,15,(.group 6 561 false)⟩)
(.leaf ⟨89218,15,(.group 6 562 false)⟩)))
(.branch 89263
(.branch 89248
(.leaf ⟨89233,15,(.group 6 563 false)⟩)
(.leaf ⟨89248,15,(.group 6 564 false)⟩))
(.branch 89278
(.leaf ⟨89263,15,(.group 6 565 false)⟩)
(.leaf ⟨89278,15,(.group 6 566 false)⟩)))))
(.branch 89413
(.branch 89353
(.branch 89323
(.branch 89308
(.leaf ⟨89293,15,(.group 6 567 false)⟩)
(.leaf ⟨89308,15,(.group 6 568 false)⟩))
(.branch 89338
(.leaf ⟨89323,15,(.group 6 569 false)⟩)
(.leaf ⟨89338,15,(.group 6 570 false)⟩)))
(.branch 89383
(.branch 89368
(.leaf ⟨89353,15,(.group 6 571 false)⟩)
(.leaf ⟨89368,15,(.group 6 572 false)⟩))
(.branch 89398
(.leaf ⟨89383,15,(.group 6 573 false)⟩)
(.leaf ⟨89398,15,(.group 6 574 false)⟩))))
(.branch 89473
(.branch 89443
(.branch 89428
(.leaf ⟨89413,15,(.group 6 575 false)⟩)
(.leaf ⟨89428,15,(.group 6 576 false)⟩))
(.branch 89458
(.leaf ⟨89443,15,(.group 6 577 false)⟩)
(.leaf ⟨89458,15,(.group 6 578 false)⟩)))
(.branch 89503
(.branch 89488
(.leaf ⟨89473,15,(.group 6 579 false)⟩)
(.leaf ⟨89488,15,(.group 6 580 false)⟩))
(.branch 89518
(.leaf ⟨89503,15,(.group 6 581 false)⟩)
(.leaf ⟨89518,15,(.group 6 582 false)⟩))))))
(.branch 89773
(.branch 89653
(.branch 89593
(.branch 89563
(.branch 89548
(.leaf ⟨89533,15,(.group 6 583 false)⟩)
(.leaf ⟨89548,15,(.group 6 584 false)⟩))
(.branch 89578
(.leaf ⟨89563,15,(.group 6 585 false)⟩)
(.leaf ⟨89578,15,(.group 6 586 false)⟩)))
(.branch 89623
(.branch 89608
(.leaf ⟨89593,15,(.group 6 587 false)⟩)
(.leaf ⟨89608,15,(.group 6 588 false)⟩))
(.branch 89638
(.leaf ⟨89623,15,(.group 6 589 false)⟩)
(.leaf ⟨89638,15,(.group 6 590 false)⟩))))
(.branch 89713
(.branch 89683
(.branch 89668
(.leaf ⟨89653,15,(.group 6 591 false)⟩)
(.leaf ⟨89668,15,(.group 6 592 false)⟩))
(.branch 89698
(.leaf ⟨89683,15,(.group 6 593 false)⟩)
(.leaf ⟨89698,15,(.group 6 594 false)⟩)))
(.branch 89743
(.branch 89728
(.leaf ⟨89713,15,(.group 6 595 false)⟩)
(.leaf ⟨89728,15,(.group 6 596 false)⟩))
(.branch 89758
(.leaf ⟨89743,15,(.group 6 597 false)⟩)
(.leaf ⟨89758,15,(.group 6 598 false)⟩)))))
(.branch 89893
(.branch 89833
(.branch 89803
(.branch 89788
(.leaf ⟨89773,15,(.group 6 599 false)⟩)
(.leaf ⟨89788,15,(.group 6 600 false)⟩))
(.branch 89818
(.leaf ⟨89803,15,(.group 6 601 false)⟩)
(.leaf ⟨89818,15,(.group 6 602 false)⟩)))
(.branch 89863
(.branch 89848
(.leaf ⟨89833,15,(.group 6 603 false)⟩)
(.leaf ⟨89848,15,(.group 6 604 false)⟩))
(.branch 89878
(.leaf ⟨89863,15,(.group 6 605 false)⟩)
(.leaf ⟨89878,15,(.group 6 606 false)⟩))))
(.branch 89953
(.branch 89923
(.branch 89908
(.leaf ⟨89893,15,(.group 6 607 false)⟩)
(.leaf ⟨89908,15,(.group 6 608 false)⟩))
(.branch 89938
(.leaf ⟨89923,15,(.group 6 609 false)⟩)
(.leaf ⟨89938,15,(.group 6 610 false)⟩)))
(.branch 89983
(.branch 89968
(.leaf ⟨89953,15,(.group 6 611 false)⟩)
(.leaf ⟨89968,15,(.group 6 612 false)⟩))
(.branch 89998
(.leaf ⟨89983,15,(.group 6 613 false)⟩)
(.leaf ⟨89998,15,(.group 6 614 false)⟩)))))))

theorem tree92_checked : tree92.check 89053 90013 = true := by decide +kernel

def tree93 : Tree := (.branch 90493
(.branch 90253
(.branch 90133
(.branch 90073
(.branch 90043
(.branch 90028
(.leaf ⟨90013,15,(.group 6 615 false)⟩)
(.leaf ⟨90028,15,(.group 6 616 false)⟩))
(.branch 90058
(.leaf ⟨90043,15,(.group 6 617 false)⟩)
(.leaf ⟨90058,15,(.group 6 618 false)⟩)))
(.branch 90103
(.branch 90088
(.leaf ⟨90073,15,(.group 6 619 false)⟩)
(.leaf ⟨90088,15,(.group 6 620 false)⟩))
(.branch 90118
(.leaf ⟨90103,15,(.group 6 621 false)⟩)
(.leaf ⟨90118,15,(.group 6 622 false)⟩))))
(.branch 90193
(.branch 90163
(.branch 90148
(.leaf ⟨90133,15,(.group 6 623 false)⟩)
(.leaf ⟨90148,15,(.group 6 624 false)⟩))
(.branch 90178
(.leaf ⟨90163,15,(.group 6 625 false)⟩)
(.leaf ⟨90178,15,(.group 6 626 false)⟩)))
(.branch 90223
(.branch 90208
(.leaf ⟨90193,15,(.group 6 627 false)⟩)
(.leaf ⟨90208,15,(.group 6 628 false)⟩))
(.branch 90238
(.leaf ⟨90223,15,(.group 6 629 false)⟩)
(.leaf ⟨90238,15,(.group 6 630 false)⟩)))))
(.branch 90373
(.branch 90313
(.branch 90283
(.branch 90268
(.leaf ⟨90253,15,(.group 6 631 false)⟩)
(.leaf ⟨90268,15,(.group 6 632 false)⟩))
(.branch 90298
(.leaf ⟨90283,15,(.group 6 633 false)⟩)
(.leaf ⟨90298,15,(.group 6 634 false)⟩)))
(.branch 90343
(.branch 90328
(.leaf ⟨90313,15,(.group 6 635 false)⟩)
(.leaf ⟨90328,15,(.group 6 636 false)⟩))
(.branch 90358
(.leaf ⟨90343,15,(.group 6 637 false)⟩)
(.leaf ⟨90358,15,(.group 6 638 false)⟩))))
(.branch 90433
(.branch 90403
(.branch 90388
(.leaf ⟨90373,15,(.group 6 639 false)⟩)
(.leaf ⟨90388,15,(.group 6 640 false)⟩))
(.branch 90418
(.leaf ⟨90403,15,(.group 6 641 false)⟩)
(.leaf ⟨90418,15,(.group 6 642 false)⟩)))
(.branch 90463
(.branch 90448
(.leaf ⟨90433,15,(.group 6 643 false)⟩)
(.leaf ⟨90448,15,(.group 6 644 false)⟩))
(.branch 90478
(.leaf ⟨90463,15,(.group 6 645 false)⟩)
(.leaf ⟨90478,15,(.group 6 646 false)⟩))))))
(.branch 90733
(.branch 90613
(.branch 90553
(.branch 90523
(.branch 90508
(.leaf ⟨90493,15,(.group 6 647 false)⟩)
(.leaf ⟨90508,15,(.group 6 648 false)⟩))
(.branch 90538
(.leaf ⟨90523,15,(.group 6 649 false)⟩)
(.leaf ⟨90538,15,(.group 6 650 false)⟩)))
(.branch 90583
(.branch 90568
(.leaf ⟨90553,15,(.group 6 651 false)⟩)
(.leaf ⟨90568,15,(.group 6 652 false)⟩))
(.branch 90598
(.leaf ⟨90583,15,(.group 6 653 false)⟩)
(.leaf ⟨90598,15,(.group 6 654 false)⟩))))
(.branch 90673
(.branch 90643
(.branch 90628
(.leaf ⟨90613,15,(.group 6 655 false)⟩)
(.leaf ⟨90628,15,(.group 6 656 false)⟩))
(.branch 90658
(.leaf ⟨90643,15,(.group 6 657 false)⟩)
(.leaf ⟨90658,15,(.group 6 658 false)⟩)))
(.branch 90703
(.branch 90688
(.leaf ⟨90673,15,(.group 6 659 false)⟩)
(.leaf ⟨90688,15,(.group 6 660 false)⟩))
(.branch 90718
(.leaf ⟨90703,15,(.group 6 661 false)⟩)
(.leaf ⟨90718,15,(.group 6 662 false)⟩)))))
(.branch 90853
(.branch 90793
(.branch 90763
(.branch 90748
(.leaf ⟨90733,15,(.group 6 663 false)⟩)
(.leaf ⟨90748,15,(.group 6 664 false)⟩))
(.branch 90778
(.leaf ⟨90763,15,(.group 6 665 false)⟩)
(.leaf ⟨90778,15,(.group 6 666 false)⟩)))
(.branch 90823
(.branch 90808
(.leaf ⟨90793,15,(.group 6 667 false)⟩)
(.leaf ⟨90808,15,(.group 6 668 false)⟩))
(.branch 90838
(.leaf ⟨90823,15,(.group 6 669 false)⟩)
(.leaf ⟨90838,15,(.group 6 670 false)⟩))))
(.branch 90913
(.branch 90883
(.branch 90868
(.leaf ⟨90853,15,(.group 6 671 false)⟩)
(.leaf ⟨90868,15,(.group 6 672 false)⟩))
(.branch 90898
(.leaf ⟨90883,15,(.group 6 673 false)⟩)
(.leaf ⟨90898,15,(.group 6 674 false)⟩)))
(.branch 90943
(.branch 90928
(.leaf ⟨90913,15,(.group 7 150 false)⟩)
(.leaf ⟨90928,15,(.group 7 151 false)⟩))
(.branch 90958
(.leaf ⟨90943,15,(.group 7 152 false)⟩)
(.leaf ⟨90958,15,(.group 7 153 false)⟩)))))))

theorem tree93_checked : tree93.check 90013 90973 = true := by decide +kernel

def tree94 : Tree := (.branch 91453
(.branch 91213
(.branch 91093
(.branch 91033
(.branch 91003
(.branch 90988
(.leaf ⟨90973,15,(.group 7 154 false)⟩)
(.leaf ⟨90988,15,(.group 7 155 false)⟩))
(.branch 91018
(.leaf ⟨91003,15,(.group 7 156 false)⟩)
(.leaf ⟨91018,15,(.group 7 157 false)⟩)))
(.branch 91063
(.branch 91048
(.leaf ⟨91033,15,(.group 7 158 false)⟩)
(.leaf ⟨91048,15,(.group 7 159 false)⟩))
(.branch 91078
(.leaf ⟨91063,15,(.group 7 160 false)⟩)
(.leaf ⟨91078,15,(.group 7 161 false)⟩))))
(.branch 91153
(.branch 91123
(.branch 91108
(.leaf ⟨91093,15,(.group 7 162 false)⟩)
(.leaf ⟨91108,15,(.group 7 163 false)⟩))
(.branch 91138
(.leaf ⟨91123,15,(.group 7 164 false)⟩)
(.leaf ⟨91138,15,(.group 7 165 false)⟩)))
(.branch 91183
(.branch 91168
(.leaf ⟨91153,15,(.group 7 166 false)⟩)
(.leaf ⟨91168,15,(.group 7 167 false)⟩))
(.branch 91198
(.leaf ⟨91183,15,(.group 7 168 false)⟩)
(.leaf ⟨91198,15,(.group 7 169 false)⟩)))))
(.branch 91333
(.branch 91273
(.branch 91243
(.branch 91228
(.leaf ⟨91213,15,(.group 7 170 false)⟩)
(.leaf ⟨91228,15,(.group 7 171 false)⟩))
(.branch 91258
(.leaf ⟨91243,15,(.group 7 172 false)⟩)
(.leaf ⟨91258,15,(.group 7 173 false)⟩)))
(.branch 91303
(.branch 91288
(.leaf ⟨91273,15,(.group 7 174 false)⟩)
(.leaf ⟨91288,15,(.group 7 175 false)⟩))
(.branch 91318
(.leaf ⟨91303,15,(.group 7 176 false)⟩)
(.leaf ⟨91318,15,(.group 7 177 false)⟩))))
(.branch 91393
(.branch 91363
(.branch 91348
(.leaf ⟨91333,15,(.group 7 178 false)⟩)
(.leaf ⟨91348,15,(.group 7 179 false)⟩))
(.branch 91378
(.leaf ⟨91363,15,(.group 7 180 false)⟩)
(.leaf ⟨91378,15,(.group 7 181 false)⟩)))
(.branch 91423
(.branch 91408
(.leaf ⟨91393,15,(.group 7 182 false)⟩)
(.leaf ⟨91408,15,(.group 7 183 false)⟩))
(.branch 91438
(.leaf ⟨91423,15,(.group 7 184 false)⟩)
(.leaf ⟨91438,15,(.group 7 185 false)⟩))))))
(.branch 91693
(.branch 91573
(.branch 91513
(.branch 91483
(.branch 91468
(.leaf ⟨91453,15,(.group 7 186 false)⟩)
(.leaf ⟨91468,15,(.group 7 187 false)⟩))
(.branch 91498
(.leaf ⟨91483,15,(.group 7 188 false)⟩)
(.leaf ⟨91498,15,(.group 7 189 false)⟩)))
(.branch 91543
(.branch 91528
(.leaf ⟨91513,15,(.group 7 190 false)⟩)
(.leaf ⟨91528,15,(.group 7 191 false)⟩))
(.branch 91558
(.leaf ⟨91543,15,(.group 7 192 false)⟩)
(.leaf ⟨91558,15,(.group 7 193 false)⟩))))
(.branch 91633
(.branch 91603
(.branch 91588
(.leaf ⟨91573,15,(.group 7 194 false)⟩)
(.leaf ⟨91588,15,(.group 7 195 false)⟩))
(.branch 91618
(.leaf ⟨91603,15,(.group 7 196 false)⟩)
(.leaf ⟨91618,15,(.group 7 197 false)⟩)))
(.branch 91663
(.branch 91648
(.leaf ⟨91633,15,(.group 8 205 false)⟩)
(.leaf ⟨91648,15,(.group 8 206 false)⟩))
(.branch 91678
(.leaf ⟨91663,15,(.group 8 207 false)⟩)
(.leaf ⟨91678,15,(.group 8 208 false)⟩)))))
(.branch 91813
(.branch 91753
(.branch 91723
(.branch 91708
(.leaf ⟨91693,15,(.group 8 209 false)⟩)
(.leaf ⟨91708,15,(.group 8 210 false)⟩))
(.branch 91738
(.leaf ⟨91723,15,(.group 8 211 false)⟩)
(.leaf ⟨91738,15,(.group 8 212 false)⟩)))
(.branch 91783
(.branch 91768
(.leaf ⟨91753,15,(.group 8 213 false)⟩)
(.leaf ⟨91768,15,(.group 8 214 false)⟩))
(.branch 91798
(.leaf ⟨91783,15,(.group 8 215 false)⟩)
(.leaf ⟨91798,15,(.group 8 216 false)⟩))))
(.branch 91873
(.branch 91843
(.branch 91828
(.leaf ⟨91813,15,(.group 8 217 false)⟩)
(.leaf ⟨91828,15,(.group 8 218 false)⟩))
(.branch 91858
(.leaf ⟨91843,15,(.group 8 219 false)⟩)
(.leaf ⟨91858,15,(.group 8 220 false)⟩)))
(.branch 91903
(.branch 91888
(.leaf ⟨91873,15,(.group 8 221 false)⟩)
(.leaf ⟨91888,15,(.group 8 222 false)⟩))
(.branch 91918
(.leaf ⟨91903,15,(.group 8 223 false)⟩)
(.leaf ⟨91918,15,(.group 8 224 false)⟩)))))))

theorem tree94_checked : tree94.check 90973 91933 = true := by decide +kernel

def tree95 : Tree := (.branch 92413
(.branch 92173
(.branch 92053
(.branch 91993
(.branch 91963
(.branch 91948
(.leaf ⟨91933,15,(.group 8 225 false)⟩)
(.leaf ⟨91948,15,(.group 8 226 false)⟩))
(.branch 91978
(.leaf ⟨91963,15,(.group 8 227 false)⟩)
(.leaf ⟨91978,15,(.group 8 228 false)⟩)))
(.branch 92023
(.branch 92008
(.leaf ⟨91993,15,(.group 8 229 false)⟩)
(.leaf ⟨92008,15,(.group 8 230 false)⟩))
(.branch 92038
(.leaf ⟨92023,15,(.group 8 231 false)⟩)
(.leaf ⟨92038,15,(.group 8 232 false)⟩))))
(.branch 92113
(.branch 92083
(.branch 92068
(.leaf ⟨92053,15,(.group 8 233 false)⟩)
(.leaf ⟨92068,15,(.group 8 234 false)⟩))
(.branch 92098
(.leaf ⟨92083,15,(.group 8 235 false)⟩)
(.leaf ⟨92098,15,(.group 8 236 false)⟩)))
(.branch 92143
(.branch 92128
(.leaf ⟨92113,15,(.group 8 237 false)⟩)
(.leaf ⟨92128,15,(.group 8 238 false)⟩))
(.branch 92158
(.leaf ⟨92143,15,(.group 8 239 false)⟩)
(.leaf ⟨92158,15,(.group 8 240 false)⟩)))))
(.branch 92293
(.branch 92233
(.branch 92203
(.branch 92188
(.leaf ⟨92173,15,(.group 8 241 false)⟩)
(.leaf ⟨92188,15,(.group 8 242 false)⟩))
(.branch 92218
(.leaf ⟨92203,15,(.group 8 243 false)⟩)
(.leaf ⟨92218,15,(.group 8 244 false)⟩)))
(.branch 92263
(.branch 92248
(.leaf ⟨92233,15,(.group 8 245 false)⟩)
(.leaf ⟨92248,15,(.group 8 246 false)⟩))
(.branch 92278
(.leaf ⟨92263,15,(.group 8 247 false)⟩)
(.leaf ⟨92278,15,(.group 8 248 false)⟩))))
(.branch 92353
(.branch 92323
(.branch 92308
(.leaf ⟨92293,15,(.group 8 249 false)⟩)
(.leaf ⟨92308,15,(.group 8 250 false)⟩))
(.branch 92338
(.leaf ⟨92323,15,(.group 8 251 false)⟩)
(.leaf ⟨92338,15,(.group 8 252 false)⟩)))
(.branch 92383
(.branch 92368
(.leaf ⟨92353,15,(.group 8 253 false)⟩)
(.leaf ⟨92368,15,(.group 8 254 false)⟩))
(.branch 92398
(.leaf ⟨92383,15,(.group 8 255 false)⟩)
(.leaf ⟨92398,15,(.group 8 256 false)⟩))))))
(.branch 92653
(.branch 92533
(.branch 92473
(.branch 92443
(.branch 92428
(.leaf ⟨92413,15,(.group 9 203 false)⟩)
(.leaf ⟨92428,15,(.group 9 204 false)⟩))
(.branch 92458
(.leaf ⟨92443,15,(.group 9 205 false)⟩)
(.leaf ⟨92458,15,(.group 9 206 false)⟩)))
(.branch 92503
(.branch 92488
(.leaf ⟨92473,15,(.group 9 207 false)⟩)
(.leaf ⟨92488,15,(.group 9 208 false)⟩))
(.branch 92518
(.leaf ⟨92503,15,(.group 9 209 false)⟩)
(.leaf ⟨92518,15,(.group 9 210 false)⟩))))
(.branch 92593
(.branch 92563
(.branch 92548
(.leaf ⟨92533,15,(.group 9 211 false)⟩)
(.leaf ⟨92548,15,(.group 9 212 false)⟩))
(.branch 92578
(.leaf ⟨92563,15,(.group 9 213 false)⟩)
(.leaf ⟨92578,15,(.group 9 214 false)⟩)))
(.branch 92623
(.branch 92608
(.leaf ⟨92593,15,(.group 9 215 false)⟩)
(.leaf ⟨92608,15,(.group 9 216 false)⟩))
(.branch 92638
(.leaf ⟨92623,15,(.group 9 217 false)⟩)
(.leaf ⟨92638,15,(.group 9 218 false)⟩)))))
(.branch 92779
(.branch 92715
(.branch 92683
(.branch 92668
(.leaf ⟨92653,15,(.group 9 219 false)⟩)
(.leaf ⟨92668,15,(.group 9 220 false)⟩))
(.branch 92699
(.leaf ⟨92683,16,(.group 0 438 false)⟩)
(.leaf ⟨92699,16,(.group 0 439 false)⟩)))
(.branch 92747
(.branch 92731
(.leaf ⟨92715,16,(.group 0 440 false)⟩)
(.leaf ⟨92731,16,(.group 0 441 false)⟩))
(.branch 92763
(.leaf ⟨92747,16,(.group 0 442 false)⟩)
(.leaf ⟨92763,16,(.group 0 443 false)⟩))))
(.branch 92843
(.branch 92811
(.branch 92795
(.leaf ⟨92779,16,(.group 0 444 false)⟩)
(.leaf ⟨92795,16,(.group 0 445 false)⟩))
(.branch 92827
(.leaf ⟨92811,16,(.group 0 446 false)⟩)
(.leaf ⟨92827,16,(.group 0 447 false)⟩)))
(.branch 92875
(.branch 92859
(.leaf ⟨92843,16,(.group 0 448 false)⟩)
(.leaf ⟨92859,16,(.group 0 449 false)⟩))
(.branch 92891
(.leaf ⟨92875,16,(.group 0 450 false)⟩)
(.leaf ⟨92891,16,(.group 0 451 false)⟩)))))))

theorem tree95_checked : tree95.check 91933 92907 = true := by decide +kernel

def tree96 : Tree := (.branch 93419
(.branch 93163
(.branch 93035
(.branch 92971
(.branch 92939
(.branch 92923
(.leaf ⟨92907,16,(.group 0 452 false)⟩)
(.leaf ⟨92923,16,(.group 0 453 false)⟩))
(.branch 92955
(.leaf ⟨92939,16,(.group 0 454 false)⟩)
(.leaf ⟨92955,16,(.group 0 455 false)⟩)))
(.branch 93003
(.branch 92987
(.leaf ⟨92971,16,(.group 0 456 false)⟩)
(.leaf ⟨92987,16,(.group 0 457 false)⟩))
(.branch 93019
(.leaf ⟨93003,16,(.group 0 458 false)⟩)
(.leaf ⟨93019,16,(.group 0 459 false)⟩))))
(.branch 93099
(.branch 93067
(.branch 93051
(.leaf ⟨93035,16,(.group 0 460 false)⟩)
(.leaf ⟨93051,16,(.group 0 461 false)⟩))
(.branch 93083
(.leaf ⟨93067,16,(.group 0 462 false)⟩)
(.leaf ⟨93083,16,(.group 0 463 false)⟩)))
(.branch 93131
(.branch 93115
(.leaf ⟨93099,16,(.group 0 464 false)⟩)
(.leaf ⟨93115,16,(.group 0 465 false)⟩))
(.branch 93147
(.leaf ⟨93131,16,(.group 0 466 false)⟩)
(.leaf ⟨93147,16,(.group 0 467 false)⟩)))))
(.branch 93291
(.branch 93227
(.branch 93195
(.branch 93179
(.leaf ⟨93163,16,(.group 0 468 false)⟩)
(.leaf ⟨93179,16,(.group 0 469 false)⟩))
(.branch 93211
(.leaf ⟨93195,16,(.group 0 470 false)⟩)
(.leaf ⟨93211,16,(.group 0 471 false)⟩)))
(.branch 93259
(.branch 93243
(.leaf ⟨93227,16,(.group 0 472 false)⟩)
(.leaf ⟨93243,16,(.group 0 473 false)⟩))
(.branch 93275
(.leaf ⟨93259,16,(.group 0 474 false)⟩)
(.leaf ⟨93275,16,(.group 0 475 false)⟩))))
(.branch 93355
(.branch 93323
(.branch 93307
(.leaf ⟨93291,16,(.group 0 476 false)⟩)
(.leaf ⟨93307,16,(.group 0 477 false)⟩))
(.branch 93339
(.leaf ⟨93323,16,(.group 0 478 false)⟩)
(.leaf ⟨93339,16,(.group 0 479 false)⟩)))
(.branch 93387
(.branch 93371
(.leaf ⟨93355,16,(.group 0 480 false)⟩)
(.leaf ⟨93371,16,(.group 0 481 false)⟩))
(.branch 93403
(.leaf ⟨93387,16,(.group 0 482 false)⟩)
(.leaf ⟨93403,16,(.group 0 483 false)⟩))))))
(.branch 93675
(.branch 93547
(.branch 93483
(.branch 93451
(.branch 93435
(.leaf ⟨93419,16,(.group 0 484 false)⟩)
(.leaf ⟨93435,16,(.group 0 485 false)⟩))
(.branch 93467
(.leaf ⟨93451,16,(.group 0 486 false)⟩)
(.leaf ⟨93467,16,(.group 0 487 false)⟩)))
(.branch 93515
(.branch 93499
(.leaf ⟨93483,16,(.group 0 488 false)⟩)
(.leaf ⟨93499,16,(.group 0 489 false)⟩))
(.branch 93531
(.leaf ⟨93515,16,(.group 0 490 false)⟩)
(.leaf ⟨93531,16,(.group 0 491 false)⟩))))
(.branch 93611
(.branch 93579
(.branch 93563
(.leaf ⟨93547,16,(.group 0 492 false)⟩)
(.leaf ⟨93563,16,(.group 0 493 false)⟩))
(.branch 93595
(.leaf ⟨93579,16,(.group 0 494 false)⟩)
(.leaf ⟨93595,16,(.group 0 495 false)⟩)))
(.branch 93643
(.branch 93627
(.leaf ⟨93611,16,(.group 0 496 false)⟩)
(.leaf ⟨93627,16,(.group 0 497 false)⟩))
(.branch 93659
(.leaf ⟨93643,16,(.group 0 498 false)⟩)
(.leaf ⟨93659,16,(.group 0 499 false)⟩)))))
(.branch 93803
(.branch 93739
(.branch 93707
(.branch 93691
(.leaf ⟨93675,16,(.group 0 500 false)⟩)
(.leaf ⟨93691,16,(.group 0 501 false)⟩))
(.branch 93723
(.leaf ⟨93707,16,(.group 0 502 false)⟩)
(.leaf ⟨93723,16,(.group 0 503 false)⟩)))
(.branch 93771
(.branch 93755
(.leaf ⟨93739,16,(.group 0 504 false)⟩)
(.leaf ⟨93755,16,(.group 0 505 false)⟩))
(.branch 93787
(.leaf ⟨93771,16,(.group 0 506 false)⟩)
(.leaf ⟨93787,16,(.group 0 507 false)⟩))))
(.branch 93867
(.branch 93835
(.branch 93819
(.leaf ⟨93803,16,(.group 0 508 false)⟩)
(.leaf ⟨93819,16,(.group 0 509 false)⟩))
(.branch 93851
(.leaf ⟨93835,16,(.group 0 510 false)⟩)
(.leaf ⟨93851,16,(.group 0 511 false)⟩)))
(.branch 93899
(.branch 93883
(.leaf ⟨93867,16,(.group 0 512 false)⟩)
(.leaf ⟨93883,16,(.group 0 513 false)⟩))
(.branch 93915
(.leaf ⟨93899,16,(.group 0 514 false)⟩)
(.leaf ⟨93915,16,(.group 0 515 false)⟩)))))))

theorem tree96_checked : tree96.check 92907 93931 = true := by decide +kernel

def tree97 : Tree := (.branch 94443
(.branch 94187
(.branch 94059
(.branch 93995
(.branch 93963
(.branch 93947
(.leaf ⟨93931,16,(.group 0 516 false)⟩)
(.leaf ⟨93947,16,(.group 0 517 false)⟩))
(.branch 93979
(.leaf ⟨93963,16,(.group 0 518 false)⟩)
(.leaf ⟨93979,16,(.group 0 519 false)⟩)))
(.branch 94027
(.branch 94011
(.leaf ⟨93995,16,(.group 0 520 false)⟩)
(.leaf ⟨94011,16,(.group 0 521 false)⟩))
(.branch 94043
(.leaf ⟨94027,16,(.group 0 522 false)⟩)
(.leaf ⟨94043,16,(.group 0 523 false)⟩))))
(.branch 94123
(.branch 94091
(.branch 94075
(.leaf ⟨94059,16,(.group 0 524 false)⟩)
(.leaf ⟨94075,16,(.group 0 525 false)⟩))
(.branch 94107
(.leaf ⟨94091,16,(.group 0 526 false)⟩)
(.leaf ⟨94107,16,(.group 0 527 false)⟩)))
(.branch 94155
(.branch 94139
(.leaf ⟨94123,16,(.group 0 528 false)⟩)
(.leaf ⟨94139,16,(.group 0 529 false)⟩))
(.branch 94171
(.leaf ⟨94155,16,(.group 0 530 false)⟩)
(.leaf ⟨94171,16,(.group 0 531 false)⟩)))))
(.branch 94315
(.branch 94251
(.branch 94219
(.branch 94203
(.leaf ⟨94187,16,(.group 0 532 false)⟩)
(.leaf ⟨94203,16,(.group 0 533 false)⟩))
(.branch 94235
(.leaf ⟨94219,16,(.group 0 534 false)⟩)
(.leaf ⟨94235,16,(.group 0 535 false)⟩)))
(.branch 94283
(.branch 94267
(.leaf ⟨94251,16,(.group 0 536 false)⟩)
(.leaf ⟨94267,16,(.group 0 537 false)⟩))
(.branch 94299
(.leaf ⟨94283,16,(.group 0 538 false)⟩)
(.leaf ⟨94299,16,(.group 0 539 false)⟩))))
(.branch 94379
(.branch 94347
(.branch 94331
(.leaf ⟨94315,16,(.group 0 540 false)⟩)
(.leaf ⟨94331,16,(.group 0 541 false)⟩))
(.branch 94363
(.leaf ⟨94347,16,(.group 0 542 false)⟩)
(.leaf ⟨94363,16,(.group 0 543 false)⟩)))
(.branch 94411
(.branch 94395
(.leaf ⟨94379,16,(.group 0 544 false)⟩)
(.leaf ⟨94395,16,(.group 0 545 false)⟩))
(.branch 94427
(.leaf ⟨94411,16,(.group 0 546 false)⟩)
(.leaf ⟨94427,16,(.group 0 547 false)⟩))))))
(.branch 94699
(.branch 94571
(.branch 94507
(.branch 94475
(.branch 94459
(.leaf ⟨94443,16,(.group 0 548 false)⟩)
(.leaf ⟨94459,16,(.group 0 549 false)⟩))
(.branch 94491
(.leaf ⟨94475,16,(.group 0 550 false)⟩)
(.leaf ⟨94491,16,(.group 0 551 false)⟩)))
(.branch 94539
(.branch 94523
(.leaf ⟨94507,16,(.group 0 552 false)⟩)
(.leaf ⟨94523,16,(.group 0 553 false)⟩))
(.branch 94555
(.leaf ⟨94539,16,(.group 0 554 false)⟩)
(.leaf ⟨94555,16,(.group 0 555 false)⟩))))
(.branch 94635
(.branch 94603
(.branch 94587
(.leaf ⟨94571,16,(.group 0 556 false)⟩)
(.leaf ⟨94587,16,(.group 0 557 false)⟩))
(.branch 94619
(.leaf ⟨94603,16,(.group 0 558 false)⟩)
(.leaf ⟨94619,16,(.group 0 559 false)⟩)))
(.branch 94667
(.branch 94651
(.leaf ⟨94635,16,(.group 0 560 false)⟩)
(.leaf ⟨94651,16,(.group 0 561 false)⟩))
(.branch 94683
(.leaf ⟨94667,16,(.group 0 562 false)⟩)
(.leaf ⟨94683,16,(.group 0 563 false)⟩)))))
(.branch 94827
(.branch 94763
(.branch 94731
(.branch 94715
(.leaf ⟨94699,16,(.group 0 564 false)⟩)
(.leaf ⟨94715,16,(.group 0 565 false)⟩))
(.branch 94747
(.leaf ⟨94731,16,(.group 0 566 false)⟩)
(.leaf ⟨94747,16,(.group 0 567 false)⟩)))
(.branch 94795
(.branch 94779
(.leaf ⟨94763,16,(.group 0 568 false)⟩)
(.leaf ⟨94779,16,(.group 0 569 false)⟩))
(.branch 94811
(.leaf ⟨94795,16,(.group 1 165 false)⟩)
(.leaf ⟨94811,16,(.group 1 166 false)⟩))))
(.branch 94891
(.branch 94859
(.branch 94843
(.leaf ⟨94827,16,(.group 1 167 false)⟩)
(.leaf ⟨94843,16,(.group 1 168 false)⟩))
(.branch 94875
(.leaf ⟨94859,16,(.group 1 169 false)⟩)
(.leaf ⟨94875,16,(.group 1 170 false)⟩)))
(.branch 94923
(.branch 94907
(.leaf ⟨94891,16,(.group 1 171 false)⟩)
(.leaf ⟨94907,16,(.group 1 172 false)⟩))
(.branch 94939
(.leaf ⟨94923,16,(.group 1 173 false)⟩)
(.leaf ⟨94939,16,(.group 1 174 false)⟩)))))))

theorem tree97_checked : tree97.check 93931 94955 = true := by decide +kernel

def tree98 : Tree := (.branch 95467
(.branch 95211
(.branch 95083
(.branch 95019
(.branch 94987
(.branch 94971
(.leaf ⟨94955,16,(.group 1 175 false)⟩)
(.leaf ⟨94971,16,(.group 1 176 false)⟩))
(.branch 95003
(.leaf ⟨94987,16,(.group 1 177 false)⟩)
(.leaf ⟨95003,16,(.group 1 178 false)⟩)))
(.branch 95051
(.branch 95035
(.leaf ⟨95019,16,(.group 1 179 false)⟩)
(.leaf ⟨95035,16,(.group 1 180 false)⟩))
(.branch 95067
(.leaf ⟨95051,16,(.group 1 181 false)⟩)
(.leaf ⟨95067,16,(.group 1 182 false)⟩))))
(.branch 95147
(.branch 95115
(.branch 95099
(.leaf ⟨95083,16,(.group 1 183 false)⟩)
(.leaf ⟨95099,16,(.group 1 184 false)⟩))
(.branch 95131
(.leaf ⟨95115,16,(.group 1 185 false)⟩)
(.leaf ⟨95131,16,(.group 1 186 false)⟩)))
(.branch 95179
(.branch 95163
(.leaf ⟨95147,16,(.group 1 187 false)⟩)
(.leaf ⟨95163,16,(.group 1 188 false)⟩))
(.branch 95195
(.leaf ⟨95179,16,(.group 1 189 false)⟩)
(.leaf ⟨95195,16,(.group 1 190 false)⟩)))))
(.branch 95339
(.branch 95275
(.branch 95243
(.branch 95227
(.leaf ⟨95211,16,(.group 1 191 false)⟩)
(.leaf ⟨95227,16,(.group 1 192 false)⟩))
(.branch 95259
(.leaf ⟨95243,16,(.group 1 193 false)⟩)
(.leaf ⟨95259,16,(.group 1 194 false)⟩)))
(.branch 95307
(.branch 95291
(.leaf ⟨95275,16,(.group 1 195 false)⟩)
(.leaf ⟨95291,16,(.group 1 196 false)⟩))
(.branch 95323
(.leaf ⟨95307,16,(.group 1 197 false)⟩)
(.leaf ⟨95323,16,(.group 1 198 false)⟩))))
(.branch 95403
(.branch 95371
(.branch 95355
(.leaf ⟨95339,16,(.group 1 199 false)⟩)
(.leaf ⟨95355,16,(.group 1 200 false)⟩))
(.branch 95387
(.leaf ⟨95371,16,(.group 1 201 false)⟩)
(.leaf ⟨95387,16,(.group 1 202 false)⟩)))
(.branch 95435
(.branch 95419
(.leaf ⟨95403,16,(.group 1 203 false)⟩)
(.leaf ⟨95419,16,(.group 1 204 false)⟩))
(.branch 95451
(.leaf ⟨95435,16,(.group 1 205 false)⟩)
(.leaf ⟨95451,16,(.group 1 206 false)⟩))))))
(.branch 95723
(.branch 95595
(.branch 95531
(.branch 95499
(.branch 95483
(.leaf ⟨95467,16,(.group 1 207 false)⟩)
(.leaf ⟨95483,16,(.group 1 208 false)⟩))
(.branch 95515
(.leaf ⟨95499,16,(.group 1 209 false)⟩)
(.leaf ⟨95515,16,(.group 1 210 false)⟩)))
(.branch 95563
(.branch 95547
(.leaf ⟨95531,16,(.group 1 211 false)⟩)
(.leaf ⟨95547,16,(.group 1 212 false)⟩))
(.branch 95579
(.leaf ⟨95563,16,(.group 1 213 false)⟩)
(.leaf ⟨95579,16,(.group 1 214 false)⟩))))
(.branch 95659
(.branch 95627
(.branch 95611
(.leaf ⟨95595,16,(.group 1 215 false)⟩)
(.leaf ⟨95611,16,(.group 1 216 false)⟩))
(.branch 95643
(.leaf ⟨95627,16,(.group 1 217 false)⟩)
(.leaf ⟨95643,16,(.group 1 218 false)⟩)))
(.branch 95691
(.branch 95675
(.leaf ⟨95659,16,(.group 1 219 false)⟩)
(.leaf ⟨95675,16,(.group 2 165 false)⟩))
(.branch 95707
(.leaf ⟨95691,16,(.group 2 166 false)⟩)
(.leaf ⟨95707,16,(.group 2 167 false)⟩)))))
(.branch 95851
(.branch 95787
(.branch 95755
(.branch 95739
(.leaf ⟨95723,16,(.group 2 168 false)⟩)
(.leaf ⟨95739,16,(.group 2 169 false)⟩))
(.branch 95771
(.leaf ⟨95755,16,(.group 2 170 false)⟩)
(.leaf ⟨95771,16,(.group 2 171 false)⟩)))
(.branch 95819
(.branch 95803
(.leaf ⟨95787,16,(.group 2 172 false)⟩)
(.leaf ⟨95803,16,(.group 2 173 false)⟩))
(.branch 95835
(.leaf ⟨95819,16,(.group 2 174 false)⟩)
(.leaf ⟨95835,16,(.group 2 175 false)⟩))))
(.branch 95915
(.branch 95883
(.branch 95867
(.leaf ⟨95851,16,(.group 2 176 false)⟩)
(.leaf ⟨95867,16,(.group 2 177 false)⟩))
(.branch 95899
(.leaf ⟨95883,16,(.group 2 178 false)⟩)
(.leaf ⟨95899,16,(.group 2 179 false)⟩)))
(.branch 95947
(.branch 95931
(.leaf ⟨95915,16,(.group 2 180 false)⟩)
(.leaf ⟨95931,16,(.group 2 181 false)⟩))
(.branch 95963
(.leaf ⟨95947,16,(.group 2 182 false)⟩)
(.leaf ⟨95963,16,(.group 2 183 false)⟩)))))))

theorem tree98_checked : tree98.check 94955 95979 = true := by decide +kernel

def tree99 : Tree := (.branch 96491
(.branch 96235
(.branch 96107
(.branch 96043
(.branch 96011
(.branch 95995
(.leaf ⟨95979,16,(.group 2 184 false)⟩)
(.leaf ⟨95995,16,(.group 2 185 false)⟩))
(.branch 96027
(.leaf ⟨96011,16,(.group 2 186 false)⟩)
(.leaf ⟨96027,16,(.group 2 187 false)⟩)))
(.branch 96075
(.branch 96059
(.leaf ⟨96043,16,(.group 2 188 false)⟩)
(.leaf ⟨96059,16,(.group 2 189 false)⟩))
(.branch 96091
(.leaf ⟨96075,16,(.group 2 190 false)⟩)
(.leaf ⟨96091,16,(.group 2 191 false)⟩))))
(.branch 96171
(.branch 96139
(.branch 96123
(.leaf ⟨96107,16,(.group 2 192 false)⟩)
(.leaf ⟨96123,16,(.group 2 193 false)⟩))
(.branch 96155
(.leaf ⟨96139,16,(.group 2 194 false)⟩)
(.leaf ⟨96155,16,(.group 2 195 false)⟩)))
(.branch 96203
(.branch 96187
(.leaf ⟨96171,16,(.group 2 196 false)⟩)
(.leaf ⟨96187,16,(.group 2 197 false)⟩))
(.branch 96219
(.leaf ⟨96203,16,(.group 2 198 false)⟩)
(.leaf ⟨96219,16,(.group 2 199 false)⟩)))))
(.branch 96363
(.branch 96299
(.branch 96267
(.branch 96251
(.leaf ⟨96235,16,(.group 2 200 false)⟩)
(.leaf ⟨96251,16,(.group 2 201 false)⟩))
(.branch 96283
(.leaf ⟨96267,16,(.group 2 202 false)⟩)
(.leaf ⟨96283,16,(.group 2 203 false)⟩)))
(.branch 96331
(.branch 96315
(.leaf ⟨96299,16,(.group 2 204 false)⟩)
(.leaf ⟨96315,16,(.group 2 205 false)⟩))
(.branch 96347
(.leaf ⟨96331,16,(.group 2 206 false)⟩)
(.leaf ⟨96347,16,(.group 2 207 false)⟩))))
(.branch 96427
(.branch 96395
(.branch 96379
(.leaf ⟨96363,16,(.group 2 208 false)⟩)
(.leaf ⟨96379,16,(.group 2 209 false)⟩))
(.branch 96411
(.leaf ⟨96395,16,(.group 2 210 false)⟩)
(.leaf ⟨96411,16,(.group 2 211 false)⟩)))
(.branch 96459
(.branch 96443
(.leaf ⟨96427,16,(.group 2 212 false)⟩)
(.leaf ⟨96443,16,(.group 2 213 false)⟩))
(.branch 96475
(.leaf ⟨96459,16,(.group 2 214 false)⟩)
(.leaf ⟨96475,16,(.group 2 215 false)⟩))))))
(.branch 96747
(.branch 96619
(.branch 96555
(.branch 96523
(.branch 96507
(.leaf ⟨96491,16,(.group 2 216 false)⟩)
(.leaf ⟨96507,16,(.group 2 217 false)⟩))
(.branch 96539
(.leaf ⟨96523,16,(.group 2 218 false)⟩)
(.leaf ⟨96539,16,(.group 2 219 false)⟩)))
(.branch 96587
(.branch 96571
(.leaf ⟨96555,16,(.group 3 165 false)⟩)
(.leaf ⟨96571,16,(.group 3 166 false)⟩))
(.branch 96603
(.leaf ⟨96587,16,(.group 3 167 false)⟩)
(.leaf ⟨96603,16,(.group 3 168 false)⟩))))
(.branch 96683
(.branch 96651
(.branch 96635
(.leaf ⟨96619,16,(.group 3 169 false)⟩)
(.leaf ⟨96635,16,(.group 3 170 false)⟩))
(.branch 96667
(.leaf ⟨96651,16,(.group 3 171 false)⟩)
(.leaf ⟨96667,16,(.group 3 172 false)⟩)))
(.branch 96715
(.branch 96699
(.leaf ⟨96683,16,(.group 3 173 false)⟩)
(.leaf ⟨96699,16,(.group 3 174 false)⟩))
(.branch 96731
(.leaf ⟨96715,16,(.group 3 175 false)⟩)
(.leaf ⟨96731,16,(.group 3 176 false)⟩)))))
(.branch 96875
(.branch 96811
(.branch 96779
(.branch 96763
(.leaf ⟨96747,16,(.group 3 177 false)⟩)
(.leaf ⟨96763,16,(.group 3 178 false)⟩))
(.branch 96795
(.leaf ⟨96779,16,(.group 3 179 false)⟩)
(.leaf ⟨96795,16,(.group 3 180 false)⟩)))
(.branch 96843
(.branch 96827
(.leaf ⟨96811,16,(.group 3 181 false)⟩)
(.leaf ⟨96827,16,(.group 3 182 false)⟩))
(.branch 96859
(.leaf ⟨96843,16,(.group 3 183 false)⟩)
(.leaf ⟨96859,16,(.group 3 184 false)⟩))))
(.branch 96939
(.branch 96907
(.branch 96891
(.leaf ⟨96875,16,(.group 3 185 false)⟩)
(.leaf ⟨96891,16,(.group 3 186 false)⟩))
(.branch 96923
(.leaf ⟨96907,16,(.group 3 187 false)⟩)
(.leaf ⟨96923,16,(.group 3 188 false)⟩)))
(.branch 96971
(.branch 96955
(.leaf ⟨96939,16,(.group 3 189 false)⟩)
(.leaf ⟨96955,16,(.group 3 190 false)⟩))
(.branch 96987
(.leaf ⟨96971,16,(.group 3 191 false)⟩)
(.leaf ⟨96987,16,(.group 3 192 false)⟩)))))))

theorem tree99_checked : tree99.check 95979 97003 = true := by decide +kernel

def tree100 : Tree := (.branch 97515
(.branch 97259
(.branch 97131
(.branch 97067
(.branch 97035
(.branch 97019
(.leaf ⟨97003,16,(.group 3 193 false)⟩)
(.leaf ⟨97019,16,(.group 3 194 false)⟩))
(.branch 97051
(.leaf ⟨97035,16,(.group 3 195 false)⟩)
(.leaf ⟨97051,16,(.group 3 196 false)⟩)))
(.branch 97099
(.branch 97083
(.leaf ⟨97067,16,(.group 3 197 false)⟩)
(.leaf ⟨97083,16,(.group 3 198 false)⟩))
(.branch 97115
(.leaf ⟨97099,16,(.group 3 199 false)⟩)
(.leaf ⟨97115,16,(.group 3 200 false)⟩))))
(.branch 97195
(.branch 97163
(.branch 97147
(.leaf ⟨97131,16,(.group 3 201 false)⟩)
(.leaf ⟨97147,16,(.group 3 202 false)⟩))
(.branch 97179
(.leaf ⟨97163,16,(.group 3 203 false)⟩)
(.leaf ⟨97179,16,(.group 3 204 false)⟩)))
(.branch 97227
(.branch 97211
(.leaf ⟨97195,16,(.group 3 205 false)⟩)
(.leaf ⟨97211,16,(.group 3 206 false)⟩))
(.branch 97243
(.leaf ⟨97227,16,(.group 3 207 false)⟩)
(.leaf ⟨97243,16,(.group 3 208 false)⟩)))))
(.branch 97387
(.branch 97323
(.branch 97291
(.branch 97275
(.leaf ⟨97259,16,(.group 3 209 false)⟩)
(.leaf ⟨97275,16,(.group 3 210 false)⟩))
(.branch 97307
(.leaf ⟨97291,16,(.group 3 211 false)⟩)
(.leaf ⟨97307,16,(.group 3 212 false)⟩)))
(.branch 97355
(.branch 97339
(.leaf ⟨97323,16,(.group 3 213 false)⟩)
(.leaf ⟨97339,16,(.group 3 214 false)⟩))
(.branch 97371
(.leaf ⟨97355,16,(.group 3 215 false)⟩)
(.leaf ⟨97371,16,(.group 3 216 false)⟩))))
(.branch 97451
(.branch 97419
(.branch 97403
(.leaf ⟨97387,16,(.group 3 217 false)⟩)
(.leaf ⟨97403,16,(.group 3 218 false)⟩))
(.branch 97435
(.leaf ⟨97419,16,(.group 3 219 false)⟩)
(.leaf ⟨97435,16,(.group 4 165 false)⟩)))
(.branch 97483
(.branch 97467
(.leaf ⟨97451,16,(.group 4 166 false)⟩)
(.leaf ⟨97467,16,(.group 4 167 false)⟩))
(.branch 97499
(.leaf ⟨97483,16,(.group 4 168 false)⟩)
(.leaf ⟨97499,16,(.group 4 169 false)⟩))))))
(.branch 97771
(.branch 97643
(.branch 97579
(.branch 97547
(.branch 97531
(.leaf ⟨97515,16,(.group 4 170 false)⟩)
(.leaf ⟨97531,16,(.group 4 171 false)⟩))
(.branch 97563
(.leaf ⟨97547,16,(.group 4 172 false)⟩)
(.leaf ⟨97563,16,(.group 4 173 false)⟩)))
(.branch 97611
(.branch 97595
(.leaf ⟨97579,16,(.group 4 174 false)⟩)
(.leaf ⟨97595,16,(.group 4 175 false)⟩))
(.branch 97627
(.leaf ⟨97611,16,(.group 4 176 false)⟩)
(.leaf ⟨97627,16,(.group 4 177 false)⟩))))
(.branch 97707
(.branch 97675
(.branch 97659
(.leaf ⟨97643,16,(.group 4 178 false)⟩)
(.leaf ⟨97659,16,(.group 4 179 false)⟩))
(.branch 97691
(.leaf ⟨97675,16,(.group 4 180 false)⟩)
(.leaf ⟨97691,16,(.group 4 181 false)⟩)))
(.branch 97739
(.branch 97723
(.leaf ⟨97707,16,(.group 4 182 false)⟩)
(.leaf ⟨97723,16,(.group 4 183 false)⟩))
(.branch 97755
(.leaf ⟨97739,16,(.group 4 184 false)⟩)
(.leaf ⟨97755,16,(.group 4 185 false)⟩)))))
(.branch 97899
(.branch 97835
(.branch 97803
(.branch 97787
(.leaf ⟨97771,16,(.group 4 186 false)⟩)
(.leaf ⟨97787,16,(.group 4 187 false)⟩))
(.branch 97819
(.leaf ⟨97803,16,(.group 4 188 false)⟩)
(.leaf ⟨97819,16,(.group 4 189 false)⟩)))
(.branch 97867
(.branch 97851
(.leaf ⟨97835,16,(.group 4 190 false)⟩)
(.leaf ⟨97851,16,(.group 4 191 false)⟩))
(.branch 97883
(.leaf ⟨97867,16,(.group 4 192 false)⟩)
(.leaf ⟨97883,16,(.group 4 193 false)⟩))))
(.branch 97963
(.branch 97931
(.branch 97915
(.leaf ⟨97899,16,(.group 4 194 false)⟩)
(.leaf ⟨97915,16,(.group 4 195 false)⟩))
(.branch 97947
(.leaf ⟨97931,16,(.group 4 196 false)⟩)
(.leaf ⟨97947,16,(.group 4 197 false)⟩)))
(.branch 97995
(.branch 97979
(.leaf ⟨97963,16,(.group 4 198 false)⟩)
(.leaf ⟨97979,16,(.group 4 199 false)⟩))
(.branch 98011
(.leaf ⟨97995,16,(.group 4 200 false)⟩)
(.leaf ⟨98011,16,(.group 4 201 false)⟩)))))))

theorem tree100_checked : tree100.check 97003 98027 = true := by decide +kernel

def tree101 : Tree := (.branch 98539
(.branch 98283
(.branch 98155
(.branch 98091
(.branch 98059
(.branch 98043
(.leaf ⟨98027,16,(.group 4 202 false)⟩)
(.leaf ⟨98043,16,(.group 4 203 false)⟩))
(.branch 98075
(.leaf ⟨98059,16,(.group 4 204 false)⟩)
(.leaf ⟨98075,16,(.group 4 205 false)⟩)))
(.branch 98123
(.branch 98107
(.leaf ⟨98091,16,(.group 4 206 false)⟩)
(.leaf ⟨98107,16,(.group 4 207 false)⟩))
(.branch 98139
(.leaf ⟨98123,16,(.group 4 208 false)⟩)
(.leaf ⟨98139,16,(.group 4 209 false)⟩))))
(.branch 98219
(.branch 98187
(.branch 98171
(.leaf ⟨98155,16,(.group 4 210 false)⟩)
(.leaf ⟨98171,16,(.group 4 211 false)⟩))
(.branch 98203
(.leaf ⟨98187,16,(.group 4 212 false)⟩)
(.leaf ⟨98203,16,(.group 4 213 false)⟩)))
(.branch 98251
(.branch 98235
(.leaf ⟨98219,16,(.group 4 214 false)⟩)
(.leaf ⟨98235,16,(.group 4 215 false)⟩))
(.branch 98267
(.leaf ⟨98251,16,(.group 4 216 false)⟩)
(.leaf ⟨98267,16,(.group 4 217 false)⟩)))))
(.branch 98411
(.branch 98347
(.branch 98315
(.branch 98299
(.leaf ⟨98283,16,(.group 4 218 false)⟩)
(.leaf ⟨98299,16,(.group 4 219 false)⟩))
(.branch 98331
(.leaf ⟨98315,16,(.group 5 1215 false)⟩)
(.leaf ⟨98331,16,(.group 5 1216 false)⟩)))
(.branch 98379
(.branch 98363
(.leaf ⟨98347,16,(.group 5 1217 false)⟩)
(.leaf ⟨98363,16,(.group 5 1218 false)⟩))
(.branch 98395
(.leaf ⟨98379,16,(.group 5 1219 false)⟩)
(.leaf ⟨98395,16,(.group 5 1220 false)⟩))))
(.branch 98475
(.branch 98443
(.branch 98427
(.leaf ⟨98411,16,(.group 5 1221 false)⟩)
(.leaf ⟨98427,16,(.group 5 1222 false)⟩))
(.branch 98459
(.leaf ⟨98443,16,(.group 5 1223 false)⟩)
(.leaf ⟨98459,16,(.group 5 1224 false)⟩)))
(.branch 98507
(.branch 98491
(.leaf ⟨98475,16,(.group 5 1225 false)⟩)
(.leaf ⟨98491,16,(.group 5 1226 false)⟩))
(.branch 98523
(.leaf ⟨98507,16,(.group 5 1227 false)⟩)
(.leaf ⟨98523,16,(.group 5 1228 false)⟩))))))
(.branch 98795
(.branch 98667
(.branch 98603
(.branch 98571
(.branch 98555
(.leaf ⟨98539,16,(.group 5 1229 false)⟩)
(.leaf ⟨98555,16,(.group 5 1230 false)⟩))
(.branch 98587
(.leaf ⟨98571,16,(.group 5 1231 false)⟩)
(.leaf ⟨98587,16,(.group 5 1232 false)⟩)))
(.branch 98635
(.branch 98619
(.leaf ⟨98603,16,(.group 5 1233 false)⟩)
(.leaf ⟨98619,16,(.group 5 1234 false)⟩))
(.branch 98651
(.leaf ⟨98635,16,(.group 5 1235 false)⟩)
(.leaf ⟨98651,16,(.group 5 1236 false)⟩))))
(.branch 98731
(.branch 98699
(.branch 98683
(.leaf ⟨98667,16,(.group 5 1237 false)⟩)
(.leaf ⟨98683,16,(.group 5 1238 false)⟩))
(.branch 98715
(.leaf ⟨98699,16,(.group 5 1239 false)⟩)
(.leaf ⟨98715,16,(.group 5 1240 false)⟩)))
(.branch 98763
(.branch 98747
(.leaf ⟨98731,16,(.group 5 1241 false)⟩)
(.leaf ⟨98747,16,(.group 5 1242 false)⟩))
(.branch 98779
(.leaf ⟨98763,16,(.group 5 1243 false)⟩)
(.leaf ⟨98779,16,(.group 5 1244 false)⟩)))))
(.branch 98923
(.branch 98859
(.branch 98827
(.branch 98811
(.leaf ⟨98795,16,(.group 5 1245 false)⟩)
(.leaf ⟨98811,16,(.group 5 1246 false)⟩))
(.branch 98843
(.leaf ⟨98827,16,(.group 5 1247 false)⟩)
(.leaf ⟨98843,16,(.group 5 1248 false)⟩)))
(.branch 98891
(.branch 98875
(.leaf ⟨98859,16,(.group 5 1249 false)⟩)
(.leaf ⟨98875,16,(.group 5 1250 false)⟩))
(.branch 98907
(.leaf ⟨98891,16,(.group 5 1251 false)⟩)
(.leaf ⟨98907,16,(.group 5 1252 false)⟩))))
(.branch 98987
(.branch 98955
(.branch 98939
(.leaf ⟨98923,16,(.group 5 1253 false)⟩)
(.leaf ⟨98939,16,(.group 5 1254 false)⟩))
(.branch 98971
(.leaf ⟨98955,16,(.group 5 1255 false)⟩)
(.leaf ⟨98971,16,(.group 5 1256 false)⟩)))
(.branch 99019
(.branch 99003
(.leaf ⟨98987,16,(.group 5 1257 false)⟩)
(.leaf ⟨99003,16,(.group 5 1258 false)⟩))
(.branch 99035
(.leaf ⟨99019,16,(.group 5 1259 false)⟩)
(.leaf ⟨99035,16,(.group 5 1260 false)⟩)))))))

theorem tree101_checked : tree101.check 98027 99051 = true := by decide +kernel

def tree102 : Tree := (.branch 99563
(.branch 99307
(.branch 99179
(.branch 99115
(.branch 99083
(.branch 99067
(.leaf ⟨99051,16,(.group 5 1261 false)⟩)
(.leaf ⟨99067,16,(.group 5 1262 false)⟩))
(.branch 99099
(.leaf ⟨99083,16,(.group 5 1263 false)⟩)
(.leaf ⟨99099,16,(.group 5 1264 false)⟩)))
(.branch 99147
(.branch 99131
(.leaf ⟨99115,16,(.group 5 1265 false)⟩)
(.leaf ⟨99131,16,(.group 5 1266 false)⟩))
(.branch 99163
(.leaf ⟨99147,16,(.group 5 1267 false)⟩)
(.leaf ⟨99163,16,(.group 5 1268 false)⟩))))
(.branch 99243
(.branch 99211
(.branch 99195
(.leaf ⟨99179,16,(.group 5 1269 false)⟩)
(.leaf ⟨99195,16,(.group 5 1270 false)⟩))
(.branch 99227
(.leaf ⟨99211,16,(.group 5 1271 false)⟩)
(.leaf ⟨99227,16,(.group 5 1272 false)⟩)))
(.branch 99275
(.branch 99259
(.leaf ⟨99243,16,(.group 5 1273 false)⟩)
(.leaf ⟨99259,16,(.group 5 1274 false)⟩))
(.branch 99291
(.leaf ⟨99275,16,(.group 5 1275 false)⟩)
(.leaf ⟨99291,16,(.group 5 1276 false)⟩)))))
(.branch 99435
(.branch 99371
(.branch 99339
(.branch 99323
(.leaf ⟨99307,16,(.group 5 1277 false)⟩)
(.leaf ⟨99323,16,(.group 5 1278 false)⟩))
(.branch 99355
(.leaf ⟨99339,16,(.group 5 1279 false)⟩)
(.leaf ⟨99355,16,(.group 5 1280 false)⟩)))
(.branch 99403
(.branch 99387
(.leaf ⟨99371,16,(.group 5 1281 false)⟩)
(.leaf ⟨99387,16,(.group 5 1282 false)⟩))
(.branch 99419
(.leaf ⟨99403,16,(.group 5 1283 false)⟩)
(.leaf ⟨99419,16,(.group 5 1284 false)⟩))))
(.branch 99499
(.branch 99467
(.branch 99451
(.leaf ⟨99435,16,(.group 5 1285 false)⟩)
(.leaf ⟨99451,16,(.group 5 1286 false)⟩))
(.branch 99483
(.leaf ⟨99467,16,(.group 5 1287 false)⟩)
(.leaf ⟨99483,16,(.group 5 1288 false)⟩)))
(.branch 99531
(.branch 99515
(.leaf ⟨99499,16,(.group 5 1289 false)⟩)
(.leaf ⟨99515,16,(.group 5 1290 false)⟩))
(.branch 99547
(.leaf ⟨99531,16,(.group 5 1291 false)⟩)
(.leaf ⟨99547,16,(.group 5 1292 false)⟩))))))
(.branch 99819
(.branch 99691
(.branch 99627
(.branch 99595
(.branch 99579
(.leaf ⟨99563,16,(.group 5 1293 false)⟩)
(.leaf ⟨99579,16,(.group 5 1294 false)⟩))
(.branch 99611
(.leaf ⟨99595,16,(.group 5 1295 false)⟩)
(.leaf ⟨99611,16,(.group 5 1296 false)⟩)))
(.branch 99659
(.branch 99643
(.leaf ⟨99627,16,(.group 5 1297 false)⟩)
(.leaf ⟨99643,16,(.group 5 1298 false)⟩))
(.branch 99675
(.leaf ⟨99659,16,(.group 5 1299 false)⟩)
(.leaf ⟨99675,16,(.group 5 1300 false)⟩))))
(.branch 99755
(.branch 99723
(.branch 99707
(.leaf ⟨99691,16,(.group 5 1301 false)⟩)
(.leaf ⟨99707,16,(.group 5 1302 false)⟩))
(.branch 99739
(.leaf ⟨99723,16,(.group 5 1303 false)⟩)
(.leaf ⟨99739,16,(.group 5 1304 false)⟩)))
(.branch 99787
(.branch 99771
(.leaf ⟨99755,16,(.group 5 1305 false)⟩)
(.leaf ⟨99771,16,(.group 5 1306 false)⟩))
(.branch 99803
(.leaf ⟨99787,16,(.group 5 1307 false)⟩)
(.leaf ⟨99803,16,(.group 5 1308 false)⟩)))))
(.branch 99947
(.branch 99883
(.branch 99851
(.branch 99835
(.leaf ⟨99819,16,(.group 5 1309 false)⟩)
(.leaf ⟨99835,16,(.group 5 1310 false)⟩))
(.branch 99867
(.leaf ⟨99851,16,(.group 5 1311 false)⟩)
(.leaf ⟨99867,16,(.group 5 1312 false)⟩)))
(.branch 99915
(.branch 99899
(.leaf ⟨99883,16,(.group 5 1313 false)⟩)
(.leaf ⟨99899,16,(.group 5 1314 false)⟩))
(.branch 99931
(.leaf ⟨99915,16,(.group 5 1315 false)⟩)
(.leaf ⟨99931,16,(.group 5 1316 false)⟩))))
(.branch 100011
(.branch 99979
(.branch 99963
(.leaf ⟨99947,16,(.group 5 1317 false)⟩)
(.leaf ⟨99963,16,(.group 5 1318 false)⟩))
(.branch 99995
(.leaf ⟨99979,16,(.group 5 1319 false)⟩)
(.leaf ⟨99995,16,(.group 5 1320 false)⟩)))
(.branch 100043
(.branch 100027
(.leaf ⟨100011,16,(.group 5 1321 false)⟩)
(.leaf ⟨100027,16,(.group 5 1322 false)⟩))
(.branch 100059
(.leaf ⟨100043,16,(.group 5 1323 false)⟩)
(.leaf ⟨100059,16,(.group 5 1324 false)⟩)))))))

theorem tree102_checked : tree102.check 99051 100075 = true := by decide +kernel

def tree103 : Tree := (.branch 100587
(.branch 100331
(.branch 100203
(.branch 100139
(.branch 100107
(.branch 100091
(.leaf ⟨100075,16,(.group 5 1325 false)⟩)
(.leaf ⟨100091,16,(.group 5 1326 false)⟩))
(.branch 100123
(.leaf ⟨100107,16,(.group 5 1327 false)⟩)
(.leaf ⟨100123,16,(.group 5 1328 false)⟩)))
(.branch 100171
(.branch 100155
(.leaf ⟨100139,16,(.group 5 1329 false)⟩)
(.leaf ⟨100155,16,(.group 5 1330 false)⟩))
(.branch 100187
(.leaf ⟨100171,16,(.group 5 1331 false)⟩)
(.leaf ⟨100187,16,(.group 5 1332 false)⟩))))
(.branch 100267
(.branch 100235
(.branch 100219
(.leaf ⟨100203,16,(.group 5 1333 false)⟩)
(.leaf ⟨100219,16,(.group 5 1334 false)⟩))
(.branch 100251
(.leaf ⟨100235,16,(.group 5 1335 false)⟩)
(.leaf ⟨100251,16,(.group 5 1336 false)⟩)))
(.branch 100299
(.branch 100283
(.leaf ⟨100267,16,(.group 5 1337 false)⟩)
(.leaf ⟨100283,16,(.group 5 1338 false)⟩))
(.branch 100315
(.leaf ⟨100299,16,(.group 5 1339 false)⟩)
(.leaf ⟨100315,16,(.group 5 1340 false)⟩)))))
(.branch 100459
(.branch 100395
(.branch 100363
(.branch 100347
(.leaf ⟨100331,16,(.group 5 1341 false)⟩)
(.leaf ⟨100347,16,(.group 5 1342 false)⟩))
(.branch 100379
(.leaf ⟨100363,16,(.group 5 1343 false)⟩)
(.leaf ⟨100379,16,(.group 5 1344 false)⟩)))
(.branch 100427
(.branch 100411
(.leaf ⟨100395,16,(.group 5 1345 false)⟩)
(.leaf ⟨100411,16,(.group 5 1346 false)⟩))
(.branch 100443
(.leaf ⟨100427,16,(.group 5 1347 false)⟩)
(.leaf ⟨100443,16,(.group 5 1348 false)⟩))))
(.branch 100523
(.branch 100491
(.branch 100475
(.leaf ⟨100459,16,(.group 5 1349 false)⟩)
(.leaf ⟨100475,16,(.group 5 1350 false)⟩))
(.branch 100507
(.leaf ⟨100491,16,(.group 5 1351 false)⟩)
(.leaf ⟨100507,16,(.group 5 1352 false)⟩)))
(.branch 100555
(.branch 100539
(.leaf ⟨100523,16,(.group 5 1353 false)⟩)
(.leaf ⟨100539,16,(.group 5 1354 false)⟩))
(.branch 100571
(.leaf ⟨100555,16,(.group 5 1355 false)⟩)
(.leaf ⟨100571,16,(.group 5 1356 false)⟩))))))
(.branch 100843
(.branch 100715
(.branch 100651
(.branch 100619
(.branch 100603
(.leaf ⟨100587,16,(.group 5 1357 false)⟩)
(.leaf ⟨100603,16,(.group 5 1358 false)⟩))
(.branch 100635
(.leaf ⟨100619,16,(.group 5 1359 false)⟩)
(.leaf ⟨100635,16,(.group 5 1360 false)⟩)))
(.branch 100683
(.branch 100667
(.leaf ⟨100651,16,(.group 5 1361 false)⟩)
(.leaf ⟨100667,16,(.group 5 1362 false)⟩))
(.branch 100699
(.leaf ⟨100683,16,(.group 5 1363 false)⟩)
(.leaf ⟨100699,16,(.group 5 1364 false)⟩))))
(.branch 100779
(.branch 100747
(.branch 100731
(.leaf ⟨100715,16,(.group 5 1365 false)⟩)
(.leaf ⟨100731,16,(.group 5 1366 false)⟩))
(.branch 100763
(.leaf ⟨100747,16,(.group 5 1367 false)⟩)
(.leaf ⟨100763,16,(.group 5 1368 false)⟩)))
(.branch 100811
(.branch 100795
(.leaf ⟨100779,16,(.group 5 1369 false)⟩)
(.leaf ⟨100795,16,(.group 5 1370 false)⟩))
(.branch 100827
(.leaf ⟨100811,16,(.group 5 1371 false)⟩)
(.leaf ⟨100827,16,(.group 5 1372 false)⟩)))))
(.branch 100971
(.branch 100907
(.branch 100875
(.branch 100859
(.leaf ⟨100843,16,(.group 5 1373 false)⟩)
(.leaf ⟨100859,16,(.group 5 1374 false)⟩))
(.branch 100891
(.leaf ⟨100875,16,(.group 5 1375 false)⟩)
(.leaf ⟨100891,16,(.group 5 1376 false)⟩)))
(.branch 100939
(.branch 100923
(.leaf ⟨100907,16,(.group 5 1377 false)⟩)
(.leaf ⟨100923,16,(.group 5 1378 false)⟩))
(.branch 100955
(.leaf ⟨100939,16,(.group 5 1379 false)⟩)
(.leaf ⟨100955,16,(.group 5 1380 false)⟩))))
(.branch 101035
(.branch 101003
(.branch 100987
(.leaf ⟨100971,16,(.group 5 1381 false)⟩)
(.leaf ⟨100987,16,(.group 5 1382 false)⟩))
(.branch 101019
(.leaf ⟨101003,16,(.group 5 1383 false)⟩)
(.leaf ⟨101019,16,(.group 5 1384 false)⟩)))
(.branch 101067
(.branch 101051
(.leaf ⟨101035,16,(.group 5 1385 false)⟩)
(.leaf ⟨101051,16,(.group 5 1386 false)⟩))
(.branch 101083
(.leaf ⟨101067,16,(.group 5 1387 false)⟩)
(.leaf ⟨101083,16,(.group 5 1388 false)⟩)))))))

theorem tree103_checked : tree103.check 100075 101099 = true := by decide +kernel

def tree104 : Tree := (.branch 101611
(.branch 101355
(.branch 101227
(.branch 101163
(.branch 101131
(.branch 101115
(.leaf ⟨101099,16,(.group 5 1389 false)⟩)
(.leaf ⟨101115,16,(.group 5 1390 false)⟩))
(.branch 101147
(.leaf ⟨101131,16,(.group 5 1391 false)⟩)
(.leaf ⟨101147,16,(.group 5 1392 false)⟩)))
(.branch 101195
(.branch 101179
(.leaf ⟨101163,16,(.group 5 1393 false)⟩)
(.leaf ⟨101179,16,(.group 5 1394 false)⟩))
(.branch 101211
(.leaf ⟨101195,16,(.group 5 1395 false)⟩)
(.leaf ⟨101211,16,(.group 5 1396 false)⟩))))
(.branch 101291
(.branch 101259
(.branch 101243
(.leaf ⟨101227,16,(.group 5 1397 false)⟩)
(.leaf ⟨101243,16,(.group 5 1398 false)⟩))
(.branch 101275
(.leaf ⟨101259,16,(.group 5 1399 false)⟩)
(.leaf ⟨101275,16,(.group 5 1400 false)⟩)))
(.branch 101323
(.branch 101307
(.leaf ⟨101291,16,(.group 5 1401 false)⟩)
(.leaf ⟨101307,16,(.group 5 1402 false)⟩))
(.branch 101339
(.leaf ⟨101323,16,(.group 5 1403 false)⟩)
(.leaf ⟨101339,16,(.group 5 1404 false)⟩)))))
(.branch 101483
(.branch 101419
(.branch 101387
(.branch 101371
(.leaf ⟨101355,16,(.group 5 1405 false)⟩)
(.leaf ⟨101371,16,(.group 5 1406 false)⟩))
(.branch 101403
(.leaf ⟨101387,16,(.group 5 1407 false)⟩)
(.leaf ⟨101403,16,(.group 5 1408 false)⟩)))
(.branch 101451
(.branch 101435
(.leaf ⟨101419,16,(.group 5 1409 false)⟩)
(.leaf ⟨101435,16,(.group 5 1410 false)⟩))
(.branch 101467
(.leaf ⟨101451,16,(.group 5 1411 false)⟩)
(.leaf ⟨101467,16,(.group 5 1412 false)⟩))))
(.branch 101547
(.branch 101515
(.branch 101499
(.leaf ⟨101483,16,(.group 5 1413 false)⟩)
(.leaf ⟨101499,16,(.group 5 1414 false)⟩))
(.branch 101531
(.leaf ⟨101515,16,(.group 5 1415 false)⟩)
(.leaf ⟨101531,16,(.group 5 1416 false)⟩)))
(.branch 101579
(.branch 101563
(.leaf ⟨101547,16,(.group 5 1417 false)⟩)
(.leaf ⟨101563,16,(.group 5 1418 false)⟩))
(.branch 101595
(.leaf ⟨101579,16,(.group 5 1419 false)⟩)
(.leaf ⟨101595,16,(.group 5 1420 false)⟩))))))
(.branch 101867
(.branch 101739
(.branch 101675
(.branch 101643
(.branch 101627
(.leaf ⟨101611,16,(.group 5 1421 false)⟩)
(.leaf ⟨101627,16,(.group 5 1422 false)⟩))
(.branch 101659
(.leaf ⟨101643,16,(.group 5 1423 false)⟩)
(.leaf ⟨101659,16,(.group 5 1424 false)⟩)))
(.branch 101707
(.branch 101691
(.leaf ⟨101675,16,(.group 5 1425 false)⟩)
(.leaf ⟨101691,16,(.group 5 1426 false)⟩))
(.branch 101723
(.leaf ⟨101707,16,(.group 5 1427 false)⟩)
(.leaf ⟨101723,16,(.group 5 1428 false)⟩))))
(.branch 101803
(.branch 101771
(.branch 101755
(.leaf ⟨101739,16,(.group 5 1429 false)⟩)
(.leaf ⟨101755,16,(.group 5 1430 false)⟩))
(.branch 101787
(.leaf ⟨101771,16,(.group 5 1431 false)⟩)
(.leaf ⟨101787,16,(.group 5 1432 false)⟩)))
(.branch 101835
(.branch 101819
(.leaf ⟨101803,16,(.group 5 1433 false)⟩)
(.leaf ⟨101819,16,(.group 5 1434 false)⟩))
(.branch 101851
(.leaf ⟨101835,16,(.group 5 1435 false)⟩)
(.leaf ⟨101851,16,(.group 5 1436 false)⟩)))))
(.branch 101995
(.branch 101931
(.branch 101899
(.branch 101883
(.leaf ⟨101867,16,(.group 5 1437 false)⟩)
(.leaf ⟨101883,16,(.group 5 1438 false)⟩))
(.branch 101915
(.leaf ⟨101899,16,(.group 5 1439 false)⟩)
(.leaf ⟨101915,16,(.group 5 1440 false)⟩)))
(.branch 101963
(.branch 101947
(.leaf ⟨101931,16,(.group 5 1441 false)⟩)
(.leaf ⟨101947,16,(.group 5 1442 false)⟩))
(.branch 101979
(.leaf ⟨101963,16,(.group 5 1443 false)⟩)
(.leaf ⟨101979,16,(.group 5 1444 false)⟩))))
(.branch 102059
(.branch 102027
(.branch 102011
(.leaf ⟨101995,16,(.group 5 1445 false)⟩)
(.leaf ⟨102011,16,(.group 5 1446 false)⟩))
(.branch 102043
(.leaf ⟨102027,16,(.group 5 1447 false)⟩)
(.leaf ⟨102043,16,(.group 5 1448 false)⟩)))
(.branch 102091
(.branch 102075
(.leaf ⟨102059,16,(.group 5 1449 false)⟩)
(.leaf ⟨102075,16,(.group 5 1450 false)⟩))
(.branch 102107
(.leaf ⟨102091,16,(.group 5 1451 false)⟩)
(.leaf ⟨102107,16,(.group 5 1452 false)⟩)))))))

theorem tree104_checked : tree104.check 101099 102123 = true := by decide +kernel

def tree105 : Tree := (.branch 102635
(.branch 102379
(.branch 102251
(.branch 102187
(.branch 102155
(.branch 102139
(.leaf ⟨102123,16,(.group 5 1453 false)⟩)
(.leaf ⟨102139,16,(.group 5 1454 false)⟩))
(.branch 102171
(.leaf ⟨102155,16,(.group 5 1455 false)⟩)
(.leaf ⟨102171,16,(.group 5 1456 false)⟩)))
(.branch 102219
(.branch 102203
(.leaf ⟨102187,16,(.group 5 1457 false)⟩)
(.leaf ⟨102203,16,(.group 5 1458 false)⟩))
(.branch 102235
(.leaf ⟨102219,16,(.group 5 1459 false)⟩)
(.leaf ⟨102235,16,(.group 5 1460 false)⟩))))
(.branch 102315
(.branch 102283
(.branch 102267
(.leaf ⟨102251,16,(.group 5 1461 false)⟩)
(.leaf ⟨102267,16,(.group 5 1462 false)⟩))
(.branch 102299
(.leaf ⟨102283,16,(.group 5 1463 false)⟩)
(.leaf ⟨102299,16,(.group 5 1464 false)⟩)))
(.branch 102347
(.branch 102331
(.leaf ⟨102315,16,(.group 5 1465 false)⟩)
(.leaf ⟨102331,16,(.group 5 1466 false)⟩))
(.branch 102363
(.leaf ⟨102347,16,(.group 5 1467 false)⟩)
(.leaf ⟨102363,16,(.group 5 1468 false)⟩)))))
(.branch 102507
(.branch 102443
(.branch 102411
(.branch 102395
(.leaf ⟨102379,16,(.group 5 1469 false)⟩)
(.leaf ⟨102395,16,(.group 5 1470 false)⟩))
(.branch 102427
(.leaf ⟨102411,16,(.group 5 1471 false)⟩)
(.leaf ⟨102427,16,(.group 5 1472 false)⟩)))
(.branch 102475
(.branch 102459
(.leaf ⟨102443,16,(.group 5 1473 false)⟩)
(.leaf ⟨102459,16,(.group 5 1474 false)⟩))
(.branch 102491
(.leaf ⟨102475,16,(.group 5 1475 false)⟩)
(.leaf ⟨102491,16,(.group 5 1476 false)⟩))))
(.branch 102571
(.branch 102539
(.branch 102523
(.leaf ⟨102507,16,(.group 5 1477 false)⟩)
(.leaf ⟨102523,16,(.group 5 1478 false)⟩))
(.branch 102555
(.leaf ⟨102539,16,(.group 5 1479 false)⟩)
(.leaf ⟨102555,16,(.group 5 1480 false)⟩)))
(.branch 102603
(.branch 102587
(.leaf ⟨102571,16,(.group 5 1481 false)⟩)
(.leaf ⟨102587,16,(.group 5 1482 false)⟩))
(.branch 102619
(.leaf ⟨102603,16,(.group 5 1483 false)⟩)
(.leaf ⟨102619,16,(.group 5 1484 false)⟩))))))
(.branch 102891
(.branch 102763
(.branch 102699
(.branch 102667
(.branch 102651
(.leaf ⟨102635,16,(.group 5 1485 false)⟩)
(.leaf ⟨102651,16,(.group 5 1486 false)⟩))
(.branch 102683
(.leaf ⟨102667,16,(.group 5 1487 false)⟩)
(.leaf ⟨102683,16,(.group 5 1488 false)⟩)))
(.branch 102731
(.branch 102715
(.leaf ⟨102699,16,(.group 5 1489 false)⟩)
(.leaf ⟨102715,16,(.group 5 1490 false)⟩))
(.branch 102747
(.leaf ⟨102731,16,(.group 5 1491 false)⟩)
(.leaf ⟨102747,16,(.group 5 1492 false)⟩))))
(.branch 102827
(.branch 102795
(.branch 102779
(.leaf ⟨102763,16,(.group 5 1493 false)⟩)
(.leaf ⟨102779,16,(.group 5 1494 false)⟩))
(.branch 102811
(.leaf ⟨102795,16,(.group 5 1495 false)⟩)
(.leaf ⟨102811,16,(.group 5 1496 false)⟩)))
(.branch 102859
(.branch 102843
(.leaf ⟨102827,16,(.group 5 1497 false)⟩)
(.leaf ⟨102843,16,(.group 5 1498 false)⟩))
(.branch 102875
(.leaf ⟨102859,16,(.group 5 1499 false)⟩)
(.leaf ⟨102875,16,(.group 5 1500 false)⟩)))))
(.branch 103019
(.branch 102955
(.branch 102923
(.branch 102907
(.leaf ⟨102891,16,(.group 6 675 false)⟩)
(.leaf ⟨102907,16,(.group 6 676 false)⟩))
(.branch 102939
(.leaf ⟨102923,16,(.group 6 677 false)⟩)
(.leaf ⟨102939,16,(.group 6 678 false)⟩)))
(.branch 102987
(.branch 102971
(.leaf ⟨102955,16,(.group 6 679 false)⟩)
(.leaf ⟨102971,16,(.group 6 680 false)⟩))
(.branch 103003
(.leaf ⟨102987,16,(.group 6 681 false)⟩)
(.leaf ⟨103003,16,(.group 6 682 false)⟩))))
(.branch 103083
(.branch 103051
(.branch 103035
(.leaf ⟨103019,16,(.group 6 683 false)⟩)
(.leaf ⟨103035,16,(.group 6 684 false)⟩))
(.branch 103067
(.leaf ⟨103051,16,(.group 6 685 false)⟩)
(.leaf ⟨103067,16,(.group 6 686 false)⟩)))
(.branch 103115
(.branch 103099
(.leaf ⟨103083,16,(.group 6 687 false)⟩)
(.leaf ⟨103099,16,(.group 6 688 false)⟩))
(.branch 103131
(.leaf ⟨103115,16,(.group 6 689 false)⟩)
(.leaf ⟨103131,16,(.group 6 690 false)⟩)))))))

theorem tree105_checked : tree105.check 102123 103147 = true := by decide +kernel

def tree106 : Tree := (.branch 103659
(.branch 103403
(.branch 103275
(.branch 103211
(.branch 103179
(.branch 103163
(.leaf ⟨103147,16,(.group 6 691 false)⟩)
(.leaf ⟨103163,16,(.group 6 692 false)⟩))
(.branch 103195
(.leaf ⟨103179,16,(.group 6 693 false)⟩)
(.leaf ⟨103195,16,(.group 6 694 false)⟩)))
(.branch 103243
(.branch 103227
(.leaf ⟨103211,16,(.group 6 695 false)⟩)
(.leaf ⟨103227,16,(.group 6 696 false)⟩))
(.branch 103259
(.leaf ⟨103243,16,(.group 6 697 false)⟩)
(.leaf ⟨103259,16,(.group 6 698 false)⟩))))
(.branch 103339
(.branch 103307
(.branch 103291
(.leaf ⟨103275,16,(.group 6 699 false)⟩)
(.leaf ⟨103291,16,(.group 6 700 false)⟩))
(.branch 103323
(.leaf ⟨103307,16,(.group 6 701 false)⟩)
(.leaf ⟨103323,16,(.group 6 702 false)⟩)))
(.branch 103371
(.branch 103355
(.leaf ⟨103339,16,(.group 6 703 false)⟩)
(.leaf ⟨103355,16,(.group 6 704 false)⟩))
(.branch 103387
(.leaf ⟨103371,16,(.group 6 705 false)⟩)
(.leaf ⟨103387,16,(.group 6 706 false)⟩)))))
(.branch 103531
(.branch 103467
(.branch 103435
(.branch 103419
(.leaf ⟨103403,16,(.group 6 707 false)⟩)
(.leaf ⟨103419,16,(.group 6 708 false)⟩))
(.branch 103451
(.leaf ⟨103435,16,(.group 6 709 false)⟩)
(.leaf ⟨103451,16,(.group 6 710 false)⟩)))
(.branch 103499
(.branch 103483
(.leaf ⟨103467,16,(.group 6 711 false)⟩)
(.leaf ⟨103483,16,(.group 6 712 false)⟩))
(.branch 103515
(.leaf ⟨103499,16,(.group 6 713 false)⟩)
(.leaf ⟨103515,16,(.group 6 714 false)⟩))))
(.branch 103595
(.branch 103563
(.branch 103547
(.leaf ⟨103531,16,(.group 6 715 false)⟩)
(.leaf ⟨103547,16,(.group 6 716 false)⟩))
(.branch 103579
(.leaf ⟨103563,16,(.group 6 717 false)⟩)
(.leaf ⟨103579,16,(.group 6 718 false)⟩)))
(.branch 103627
(.branch 103611
(.leaf ⟨103595,16,(.group 6 719 false)⟩)
(.leaf ⟨103611,16,(.group 6 720 false)⟩))
(.branch 103643
(.leaf ⟨103627,16,(.group 6 721 false)⟩)
(.leaf ⟨103643,16,(.group 6 722 false)⟩))))))
(.branch 103915
(.branch 103787
(.branch 103723
(.branch 103691
(.branch 103675
(.leaf ⟨103659,16,(.group 6 723 false)⟩)
(.leaf ⟨103675,16,(.group 6 724 false)⟩))
(.branch 103707
(.leaf ⟨103691,16,(.group 6 725 false)⟩)
(.leaf ⟨103707,16,(.group 6 726 false)⟩)))
(.branch 103755
(.branch 103739
(.leaf ⟨103723,16,(.group 6 727 false)⟩)
(.leaf ⟨103739,16,(.group 6 728 false)⟩))
(.branch 103771
(.leaf ⟨103755,16,(.group 6 729 false)⟩)
(.leaf ⟨103771,16,(.group 6 730 false)⟩))))
(.branch 103851
(.branch 103819
(.branch 103803
(.leaf ⟨103787,16,(.group 6 731 false)⟩)
(.leaf ⟨103803,16,(.group 6 732 false)⟩))
(.branch 103835
(.leaf ⟨103819,16,(.group 6 733 false)⟩)
(.leaf ⟨103835,16,(.group 6 734 false)⟩)))
(.branch 103883
(.branch 103867
(.leaf ⟨103851,16,(.group 6 735 false)⟩)
(.leaf ⟨103867,16,(.group 6 736 false)⟩))
(.branch 103899
(.leaf ⟨103883,16,(.group 6 737 false)⟩)
(.leaf ⟨103899,16,(.group 6 738 false)⟩)))))
(.branch 104043
(.branch 103979
(.branch 103947
(.branch 103931
(.leaf ⟨103915,16,(.group 6 739 false)⟩)
(.leaf ⟨103931,16,(.group 6 740 false)⟩))
(.branch 103963
(.leaf ⟨103947,16,(.group 6 741 false)⟩)
(.leaf ⟨103963,16,(.group 6 742 false)⟩)))
(.branch 104011
(.branch 103995
(.leaf ⟨103979,16,(.group 6 743 false)⟩)
(.leaf ⟨103995,16,(.group 6 744 false)⟩))
(.branch 104027
(.leaf ⟨104011,16,(.group 6 745 false)⟩)
(.leaf ⟨104027,16,(.group 6 746 false)⟩))))
(.branch 104107
(.branch 104075
(.branch 104059
(.leaf ⟨104043,16,(.group 6 747 false)⟩)
(.leaf ⟨104059,16,(.group 6 748 false)⟩))
(.branch 104091
(.leaf ⟨104075,16,(.group 6 749 false)⟩)
(.leaf ⟨104091,16,(.group 6 750 false)⟩)))
(.branch 104139
(.branch 104123
(.leaf ⟨104107,16,(.group 6 751 false)⟩)
(.leaf ⟨104123,16,(.group 6 752 false)⟩))
(.branch 104155
(.leaf ⟨104139,16,(.group 6 753 false)⟩)
(.leaf ⟨104155,16,(.group 6 754 false)⟩)))))))

theorem tree106_checked : tree106.check 103147 104171 = true := by decide +kernel

def tree107 : Tree := (.branch 104683
(.branch 104427
(.branch 104299
(.branch 104235
(.branch 104203
(.branch 104187
(.leaf ⟨104171,16,(.group 6 755 false)⟩)
(.leaf ⟨104187,16,(.group 6 756 false)⟩))
(.branch 104219
(.leaf ⟨104203,16,(.group 6 757 false)⟩)
(.leaf ⟨104219,16,(.group 6 758 false)⟩)))
(.branch 104267
(.branch 104251
(.leaf ⟨104235,16,(.group 6 759 false)⟩)
(.leaf ⟨104251,16,(.group 6 760 false)⟩))
(.branch 104283
(.leaf ⟨104267,16,(.group 6 761 false)⟩)
(.leaf ⟨104283,16,(.group 6 762 false)⟩))))
(.branch 104363
(.branch 104331
(.branch 104315
(.leaf ⟨104299,16,(.group 6 763 false)⟩)
(.leaf ⟨104315,16,(.group 6 764 false)⟩))
(.branch 104347
(.leaf ⟨104331,16,(.group 6 765 false)⟩)
(.leaf ⟨104347,16,(.group 6 766 false)⟩)))
(.branch 104395
(.branch 104379
(.leaf ⟨104363,16,(.group 6 767 false)⟩)
(.leaf ⟨104379,16,(.group 6 768 false)⟩))
(.branch 104411
(.leaf ⟨104395,16,(.group 6 769 false)⟩)
(.leaf ⟨104411,16,(.group 6 770 false)⟩)))))
(.branch 104555
(.branch 104491
(.branch 104459
(.branch 104443
(.leaf ⟨104427,16,(.group 6 771 false)⟩)
(.leaf ⟨104443,16,(.group 6 772 false)⟩))
(.branch 104475
(.leaf ⟨104459,16,(.group 6 773 false)⟩)
(.leaf ⟨104475,16,(.group 6 774 false)⟩)))
(.branch 104523
(.branch 104507
(.leaf ⟨104491,16,(.group 6 775 false)⟩)
(.leaf ⟨104507,16,(.group 6 776 false)⟩))
(.branch 104539
(.leaf ⟨104523,16,(.group 6 777 false)⟩)
(.leaf ⟨104539,16,(.group 6 778 false)⟩))))
(.branch 104619
(.branch 104587
(.branch 104571
(.leaf ⟨104555,16,(.group 6 779 false)⟩)
(.leaf ⟨104571,16,(.group 6 780 false)⟩))
(.branch 104603
(.leaf ⟨104587,16,(.group 6 781 false)⟩)
(.leaf ⟨104603,16,(.group 6 782 false)⟩)))
(.branch 104651
(.branch 104635
(.leaf ⟨104619,16,(.group 6 783 false)⟩)
(.leaf ⟨104635,16,(.group 6 784 false)⟩))
(.branch 104667
(.leaf ⟨104651,16,(.group 6 785 false)⟩)
(.leaf ⟨104667,16,(.group 6 786 false)⟩))))))
(.branch 104939
(.branch 104811
(.branch 104747
(.branch 104715
(.branch 104699
(.leaf ⟨104683,16,(.group 6 787 false)⟩)
(.leaf ⟨104699,16,(.group 6 788 false)⟩))
(.branch 104731
(.leaf ⟨104715,16,(.group 6 789 false)⟩)
(.leaf ⟨104731,16,(.group 6 790 false)⟩)))
(.branch 104779
(.branch 104763
(.leaf ⟨104747,16,(.group 6 791 false)⟩)
(.leaf ⟨104763,16,(.group 6 792 false)⟩))
(.branch 104795
(.leaf ⟨104779,16,(.group 6 793 false)⟩)
(.leaf ⟨104795,16,(.group 6 794 false)⟩))))
(.branch 104875
(.branch 104843
(.branch 104827
(.leaf ⟨104811,16,(.group 6 795 false)⟩)
(.leaf ⟨104827,16,(.group 6 796 false)⟩))
(.branch 104859
(.leaf ⟨104843,16,(.group 6 797 false)⟩)
(.leaf ⟨104859,16,(.group 6 798 false)⟩)))
(.branch 104907
(.branch 104891
(.leaf ⟨104875,16,(.group 6 799 false)⟩)
(.leaf ⟨104891,16,(.group 6 800 false)⟩))
(.branch 104923
(.leaf ⟨104907,16,(.group 6 801 false)⟩)
(.leaf ⟨104923,16,(.group 6 802 false)⟩)))))
(.branch 105067
(.branch 105003
(.branch 104971
(.branch 104955
(.leaf ⟨104939,16,(.group 6 803 false)⟩)
(.leaf ⟨104955,16,(.group 6 804 false)⟩))
(.branch 104987
(.leaf ⟨104971,16,(.group 6 805 false)⟩)
(.leaf ⟨104987,16,(.group 6 806 false)⟩)))
(.branch 105035
(.branch 105019
(.leaf ⟨105003,16,(.group 6 807 false)⟩)
(.leaf ⟨105019,16,(.group 6 808 false)⟩))
(.branch 105051
(.leaf ⟨105035,16,(.group 6 809 false)⟩)
(.leaf ⟨105051,16,(.group 6 810 false)⟩))))
(.branch 105131
(.branch 105099
(.branch 105083
(.leaf ⟨105067,16,(.group 6 811 false)⟩)
(.leaf ⟨105083,16,(.group 6 812 false)⟩))
(.branch 105115
(.leaf ⟨105099,16,(.group 6 813 false)⟩)
(.leaf ⟨105115,16,(.group 6 814 false)⟩)))
(.branch 105163
(.branch 105147
(.leaf ⟨105131,16,(.group 6 815 false)⟩)
(.leaf ⟨105147,16,(.group 6 816 false)⟩))
(.branch 105179
(.leaf ⟨105163,16,(.group 6 817 false)⟩)
(.leaf ⟨105179,16,(.group 6 818 false)⟩)))))))

theorem tree107_checked : tree107.check 104171 105195 = true := by decide +kernel

def tree108 : Tree := (.branch 105707
(.branch 105451
(.branch 105323
(.branch 105259
(.branch 105227
(.branch 105211
(.leaf ⟨105195,16,(.group 6 819 false)⟩)
(.leaf ⟨105211,16,(.group 6 820 false)⟩))
(.branch 105243
(.leaf ⟨105227,16,(.group 6 821 false)⟩)
(.leaf ⟨105243,16,(.group 6 822 false)⟩)))
(.branch 105291
(.branch 105275
(.leaf ⟨105259,16,(.group 6 823 false)⟩)
(.leaf ⟨105275,16,(.group 6 824 false)⟩))
(.branch 105307
(.leaf ⟨105291,16,(.group 6 825 false)⟩)
(.leaf ⟨105307,16,(.group 6 826 false)⟩))))
(.branch 105387
(.branch 105355
(.branch 105339
(.leaf ⟨105323,16,(.group 6 827 false)⟩)
(.leaf ⟨105339,16,(.group 6 828 false)⟩))
(.branch 105371
(.leaf ⟨105355,16,(.group 6 829 false)⟩)
(.leaf ⟨105371,16,(.group 6 830 false)⟩)))
(.branch 105419
(.branch 105403
(.leaf ⟨105387,16,(.group 6 831 false)⟩)
(.leaf ⟨105403,16,(.group 6 832 false)⟩))
(.branch 105435
(.leaf ⟨105419,16,(.group 6 833 false)⟩)
(.leaf ⟨105435,16,(.group 6 834 false)⟩)))))
(.branch 105579
(.branch 105515
(.branch 105483
(.branch 105467
(.leaf ⟨105451,16,(.group 6 835 false)⟩)
(.leaf ⟨105467,16,(.group 6 836 false)⟩))
(.branch 105499
(.leaf ⟨105483,16,(.group 6 837 false)⟩)
(.leaf ⟨105499,16,(.group 6 838 false)⟩)))
(.branch 105547
(.branch 105531
(.leaf ⟨105515,16,(.group 6 839 false)⟩)
(.leaf ⟨105531,16,(.group 6 840 false)⟩))
(.branch 105563
(.leaf ⟨105547,16,(.group 6 841 false)⟩)
(.leaf ⟨105563,16,(.group 6 842 false)⟩))))
(.branch 105643
(.branch 105611
(.branch 105595
(.leaf ⟨105579,16,(.group 6 843 false)⟩)
(.leaf ⟨105595,16,(.group 6 844 false)⟩))
(.branch 105627
(.leaf ⟨105611,16,(.group 6 845 false)⟩)
(.leaf ⟨105627,16,(.group 6 846 false)⟩)))
(.branch 105675
(.branch 105659
(.leaf ⟨105643,16,(.group 6 847 false)⟩)
(.leaf ⟨105659,16,(.group 6 848 false)⟩))
(.branch 105691
(.leaf ⟨105675,16,(.group 6 849 false)⟩)
(.leaf ⟨105691,16,(.group 6 850 false)⟩))))))
(.branch 105963
(.branch 105835
(.branch 105771
(.branch 105739
(.branch 105723
(.leaf ⟨105707,16,(.group 6 851 false)⟩)
(.leaf ⟨105723,16,(.group 6 852 false)⟩))
(.branch 105755
(.leaf ⟨105739,16,(.group 6 853 false)⟩)
(.leaf ⟨105755,16,(.group 6 854 false)⟩)))
(.branch 105803
(.branch 105787
(.leaf ⟨105771,16,(.group 6 855 false)⟩)
(.leaf ⟨105787,16,(.group 6 856 false)⟩))
(.branch 105819
(.leaf ⟨105803,16,(.group 6 857 false)⟩)
(.leaf ⟨105819,16,(.group 6 858 false)⟩))))
(.branch 105899
(.branch 105867
(.branch 105851
(.leaf ⟨105835,16,(.group 6 859 false)⟩)
(.leaf ⟨105851,16,(.group 6 860 false)⟩))
(.branch 105883
(.leaf ⟨105867,16,(.group 6 861 false)⟩)
(.leaf ⟨105883,16,(.group 6 862 false)⟩)))
(.branch 105931
(.branch 105915
(.leaf ⟨105899,16,(.group 6 863 false)⟩)
(.leaf ⟨105915,16,(.group 6 864 false)⟩))
(.branch 105947
(.leaf ⟨105931,16,(.group 6 865 false)⟩)
(.leaf ⟨105947,16,(.group 6 866 false)⟩)))))
(.branch 106091
(.branch 106027
(.branch 105995
(.branch 105979
(.leaf ⟨105963,16,(.group 6 867 false)⟩)
(.leaf ⟨105979,16,(.group 6 868 false)⟩))
(.branch 106011
(.leaf ⟨105995,16,(.group 6 869 false)⟩)
(.leaf ⟨106011,16,(.group 6 870 false)⟩)))
(.branch 106059
(.branch 106043
(.leaf ⟨106027,16,(.group 6 871 false)⟩)
(.leaf ⟨106043,16,(.group 6 872 false)⟩))
(.branch 106075
(.leaf ⟨106059,16,(.group 6 873 false)⟩)
(.leaf ⟨106075,16,(.group 6 874 false)⟩))))
(.branch 106155
(.branch 106123
(.branch 106107
(.leaf ⟨106091,16,(.group 6 875 false)⟩)
(.leaf ⟨106107,16,(.group 6 876 false)⟩))
(.branch 106139
(.leaf ⟨106123,16,(.group 6 877 false)⟩)
(.leaf ⟨106139,16,(.group 6 878 false)⟩)))
(.branch 106187
(.branch 106171
(.leaf ⟨106155,16,(.group 6 879 false)⟩)
(.leaf ⟨106171,16,(.group 6 880 false)⟩))
(.branch 106203
(.leaf ⟨106187,16,(.group 6 881 false)⟩)
(.leaf ⟨106203,16,(.group 6 882 false)⟩)))))))

theorem tree108_checked : tree108.check 105195 106219 = true := by decide +kernel

def tree109 : Tree := (.branch 106731
(.branch 106475
(.branch 106347
(.branch 106283
(.branch 106251
(.branch 106235
(.leaf ⟨106219,16,(.group 6 883 false)⟩)
(.leaf ⟨106235,16,(.group 6 884 false)⟩))
(.branch 106267
(.leaf ⟨106251,16,(.group 6 885 false)⟩)
(.leaf ⟨106267,16,(.group 6 886 false)⟩)))
(.branch 106315
(.branch 106299
(.leaf ⟨106283,16,(.group 6 887 false)⟩)
(.leaf ⟨106299,16,(.group 6 888 false)⟩))
(.branch 106331
(.leaf ⟨106315,16,(.group 6 889 false)⟩)
(.leaf ⟨106331,16,(.group 6 890 false)⟩))))
(.branch 106411
(.branch 106379
(.branch 106363
(.leaf ⟨106347,16,(.group 6 891 false)⟩)
(.leaf ⟨106363,16,(.group 6 892 false)⟩))
(.branch 106395
(.leaf ⟨106379,16,(.group 6 893 false)⟩)
(.leaf ⟨106395,16,(.group 6 894 false)⟩)))
(.branch 106443
(.branch 106427
(.leaf ⟨106411,16,(.group 6 895 false)⟩)
(.leaf ⟨106427,16,(.group 6 896 false)⟩))
(.branch 106459
(.leaf ⟨106443,16,(.group 6 897 false)⟩)
(.leaf ⟨106459,16,(.group 6 898 false)⟩)))))
(.branch 106603
(.branch 106539
(.branch 106507
(.branch 106491
(.leaf ⟨106475,16,(.group 6 899 false)⟩)
(.leaf ⟨106491,16,(.group 6 900 false)⟩))
(.branch 106523
(.leaf ⟨106507,16,(.group 6 901 false)⟩)
(.leaf ⟨106523,16,(.group 6 902 false)⟩)))
(.branch 106571
(.branch 106555
(.leaf ⟨106539,16,(.group 6 903 false)⟩)
(.leaf ⟨106555,16,(.group 6 904 false)⟩))
(.branch 106587
(.leaf ⟨106571,16,(.group 6 905 false)⟩)
(.leaf ⟨106587,16,(.group 6 906 false)⟩))))
(.branch 106667
(.branch 106635
(.branch 106619
(.leaf ⟨106603,16,(.group 6 907 false)⟩)
(.leaf ⟨106619,16,(.group 6 908 false)⟩))
(.branch 106651
(.leaf ⟨106635,16,(.group 6 909 false)⟩)
(.leaf ⟨106651,16,(.group 6 910 false)⟩)))
(.branch 106699
(.branch 106683
(.leaf ⟨106667,16,(.group 6 911 false)⟩)
(.leaf ⟨106683,16,(.group 6 912 false)⟩))
(.branch 106715
(.leaf ⟨106699,16,(.group 6 913 false)⟩)
(.leaf ⟨106715,16,(.group 6 914 false)⟩))))))
(.branch 106987
(.branch 106859
(.branch 106795
(.branch 106763
(.branch 106747
(.leaf ⟨106731,16,(.group 6 915 false)⟩)
(.leaf ⟨106747,16,(.group 6 916 false)⟩))
(.branch 106779
(.leaf ⟨106763,16,(.group 6 917 false)⟩)
(.leaf ⟨106779,16,(.group 6 918 false)⟩)))
(.branch 106827
(.branch 106811
(.leaf ⟨106795,16,(.group 6 919 false)⟩)
(.leaf ⟨106811,16,(.group 6 920 false)⟩))
(.branch 106843
(.leaf ⟨106827,16,(.group 6 921 false)⟩)
(.leaf ⟨106843,16,(.group 6 922 false)⟩))))
(.branch 106923
(.branch 106891
(.branch 106875
(.leaf ⟨106859,16,(.group 6 923 false)⟩)
(.leaf ⟨106875,16,(.group 6 924 false)⟩))
(.branch 106907
(.leaf ⟨106891,16,(.group 6 925 false)⟩)
(.leaf ⟨106907,16,(.group 6 926 false)⟩)))
(.branch 106955
(.branch 106939
(.leaf ⟨106923,16,(.group 6 927 false)⟩)
(.leaf ⟨106939,16,(.group 6 928 false)⟩))
(.branch 106971
(.leaf ⟨106955,16,(.group 6 929 false)⟩)
(.leaf ⟨106971,16,(.group 6 930 false)⟩)))))
(.branch 107115
(.branch 107051
(.branch 107019
(.branch 107003
(.leaf ⟨106987,16,(.group 6 931 false)⟩)
(.leaf ⟨107003,16,(.group 6 932 false)⟩))
(.branch 107035
(.leaf ⟨107019,16,(.group 6 933 false)⟩)
(.leaf ⟨107035,16,(.group 6 934 false)⟩)))
(.branch 107083
(.branch 107067
(.leaf ⟨107051,16,(.group 6 935 false)⟩)
(.leaf ⟨107067,16,(.group 6 936 false)⟩))
(.branch 107099
(.leaf ⟨107083,16,(.group 6 937 false)⟩)
(.leaf ⟨107099,16,(.group 6 938 false)⟩))))
(.branch 107179
(.branch 107147
(.branch 107131
(.leaf ⟨107115,16,(.group 6 939 false)⟩)
(.leaf ⟨107131,16,(.group 6 940 false)⟩))
(.branch 107163
(.leaf ⟨107147,16,(.group 6 941 false)⟩)
(.leaf ⟨107163,16,(.group 6 942 false)⟩)))
(.branch 107211
(.branch 107195
(.leaf ⟨107179,16,(.group 6 943 false)⟩)
(.leaf ⟨107195,16,(.group 6 944 false)⟩))
(.branch 107227
(.leaf ⟨107211,16,(.group 6 945 false)⟩)
(.leaf ⟨107227,16,(.group 6 946 false)⟩)))))))

theorem tree109_checked : tree109.check 106219 107243 = true := by decide +kernel

def tree110 : Tree := (.branch 107755
(.branch 107499
(.branch 107371
(.branch 107307
(.branch 107275
(.branch 107259
(.leaf ⟨107243,16,(.group 6 947 false)⟩)
(.leaf ⟨107259,16,(.group 6 948 false)⟩))
(.branch 107291
(.leaf ⟨107275,16,(.group 6 949 false)⟩)
(.leaf ⟨107291,16,(.group 7 198 false)⟩)))
(.branch 107339
(.branch 107323
(.leaf ⟨107307,16,(.group 7 199 false)⟩)
(.leaf ⟨107323,16,(.group 7 200 false)⟩))
(.branch 107355
(.leaf ⟨107339,16,(.group 7 201 false)⟩)
(.leaf ⟨107355,16,(.group 7 202 false)⟩))))
(.branch 107435
(.branch 107403
(.branch 107387
(.leaf ⟨107371,16,(.group 7 203 false)⟩)
(.leaf ⟨107387,16,(.group 7 204 false)⟩))
(.branch 107419
(.leaf ⟨107403,16,(.group 7 205 false)⟩)
(.leaf ⟨107419,16,(.group 7 206 false)⟩)))
(.branch 107467
(.branch 107451
(.leaf ⟨107435,16,(.group 7 207 false)⟩)
(.leaf ⟨107451,16,(.group 7 208 false)⟩))
(.branch 107483
(.leaf ⟨107467,16,(.group 7 209 false)⟩)
(.leaf ⟨107483,16,(.group 7 210 false)⟩)))))
(.branch 107627
(.branch 107563
(.branch 107531
(.branch 107515
(.leaf ⟨107499,16,(.group 7 211 false)⟩)
(.leaf ⟨107515,16,(.group 7 212 false)⟩))
(.branch 107547
(.leaf ⟨107531,16,(.group 7 213 false)⟩)
(.leaf ⟨107547,16,(.group 7 214 false)⟩)))
(.branch 107595
(.branch 107579
(.leaf ⟨107563,16,(.group 7 215 false)⟩)
(.leaf ⟨107579,16,(.group 7 216 false)⟩))
(.branch 107611
(.leaf ⟨107595,16,(.group 7 217 false)⟩)
(.leaf ⟨107611,16,(.group 7 218 false)⟩))))
(.branch 107691
(.branch 107659
(.branch 107643
(.leaf ⟨107627,16,(.group 7 219 false)⟩)
(.leaf ⟨107643,16,(.group 7 220 false)⟩))
(.branch 107675
(.leaf ⟨107659,16,(.group 7 221 false)⟩)
(.leaf ⟨107675,16,(.group 7 222 false)⟩)))
(.branch 107723
(.branch 107707
(.leaf ⟨107691,16,(.group 7 223 false)⟩)
(.leaf ⟨107707,16,(.group 7 224 false)⟩))
(.branch 107739
(.leaf ⟨107723,16,(.group 7 225 false)⟩)
(.leaf ⟨107739,16,(.group 7 226 false)⟩))))))
(.branch 108011
(.branch 107883
(.branch 107819
(.branch 107787
(.branch 107771
(.leaf ⟨107755,16,(.group 7 227 false)⟩)
(.leaf ⟨107771,16,(.group 7 228 false)⟩))
(.branch 107803
(.leaf ⟨107787,16,(.group 7 229 false)⟩)
(.leaf ⟨107803,16,(.group 7 230 false)⟩)))
(.branch 107851
(.branch 107835
(.leaf ⟨107819,16,(.group 7 231 false)⟩)
(.leaf ⟨107835,16,(.group 7 232 false)⟩))
(.branch 107867
(.leaf ⟨107851,16,(.group 7 233 false)⟩)
(.leaf ⟨107867,16,(.group 7 234 false)⟩))))
(.branch 107947
(.branch 107915
(.branch 107899
(.leaf ⟨107883,16,(.group 7 235 false)⟩)
(.leaf ⟨107899,16,(.group 7 236 false)⟩))
(.branch 107931
(.leaf ⟨107915,16,(.group 7 237 false)⟩)
(.leaf ⟨107931,16,(.group 7 238 false)⟩)))
(.branch 107979
(.branch 107963
(.leaf ⟨107947,16,(.group 7 239 false)⟩)
(.leaf ⟨107963,16,(.group 7 240 false)⟩))
(.branch 107995
(.leaf ⟨107979,16,(.group 7 241 false)⟩)
(.leaf ⟨107995,16,(.group 7 242 false)⟩)))))
(.branch 108139
(.branch 108075
(.branch 108043
(.branch 108027
(.leaf ⟨108011,16,(.group 7 243 false)⟩)
(.leaf ⟨108027,16,(.group 7 244 false)⟩))
(.branch 108059
(.leaf ⟨108043,16,(.group 7 245 false)⟩)
(.leaf ⟨108059,16,(.group 7 246 false)⟩)))
(.branch 108107
(.branch 108091
(.leaf ⟨108075,16,(.group 7 247 false)⟩)
(.leaf ⟨108091,16,(.group 7 248 false)⟩))
(.branch 108123
(.leaf ⟨108107,16,(.group 7 249 false)⟩)
(.leaf ⟨108123,16,(.group 7 250 false)⟩))))
(.branch 108203
(.branch 108171
(.branch 108155
(.leaf ⟨108139,16,(.group 7 251 false)⟩)
(.leaf ⟨108155,16,(.group 7 252 false)⟩))
(.branch 108187
(.leaf ⟨108171,16,(.group 8 260 false)⟩)
(.leaf ⟨108187,16,(.group 8 261 false)⟩)))
(.branch 108235
(.branch 108219
(.leaf ⟨108203,16,(.group 8 262 false)⟩)
(.leaf ⟨108219,16,(.group 8 263 false)⟩))
(.branch 108251
(.leaf ⟨108235,16,(.group 8 264 false)⟩)
(.leaf ⟨108251,16,(.group 8 265 false)⟩)))))))

theorem tree110_checked : tree110.check 107243 108267 = true := by decide +kernel

def tree111 : Tree := (.branch 108779
(.branch 108523
(.branch 108395
(.branch 108331
(.branch 108299
(.branch 108283
(.leaf ⟨108267,16,(.group 8 266 false)⟩)
(.leaf ⟨108283,16,(.group 8 267 false)⟩))
(.branch 108315
(.leaf ⟨108299,16,(.group 8 268 false)⟩)
(.leaf ⟨108315,16,(.group 8 269 false)⟩)))
(.branch 108363
(.branch 108347
(.leaf ⟨108331,16,(.group 8 270 false)⟩)
(.leaf ⟨108347,16,(.group 8 271 false)⟩))
(.branch 108379
(.leaf ⟨108363,16,(.group 8 272 false)⟩)
(.leaf ⟨108379,16,(.group 8 273 false)⟩))))
(.branch 108459
(.branch 108427
(.branch 108411
(.leaf ⟨108395,16,(.group 8 274 false)⟩)
(.leaf ⟨108411,16,(.group 8 275 false)⟩))
(.branch 108443
(.leaf ⟨108427,16,(.group 8 276 false)⟩)
(.leaf ⟨108443,16,(.group 8 277 false)⟩)))
(.branch 108491
(.branch 108475
(.leaf ⟨108459,16,(.group 8 278 false)⟩)
(.leaf ⟨108475,16,(.group 8 279 false)⟩))
(.branch 108507
(.leaf ⟨108491,16,(.group 8 280 false)⟩)
(.leaf ⟨108507,16,(.group 8 281 false)⟩)))))
(.branch 108651
(.branch 108587
(.branch 108555
(.branch 108539
(.leaf ⟨108523,16,(.group 8 282 false)⟩)
(.leaf ⟨108539,16,(.group 8 283 false)⟩))
(.branch 108571
(.leaf ⟨108555,16,(.group 8 284 false)⟩)
(.leaf ⟨108571,16,(.group 8 285 false)⟩)))
(.branch 108619
(.branch 108603
(.leaf ⟨108587,16,(.group 8 286 false)⟩)
(.leaf ⟨108603,16,(.group 8 287 false)⟩))
(.branch 108635
(.leaf ⟨108619,16,(.group 8 288 false)⟩)
(.leaf ⟨108635,16,(.group 8 289 false)⟩))))
(.branch 108715
(.branch 108683
(.branch 108667
(.leaf ⟨108651,16,(.group 8 290 false)⟩)
(.leaf ⟨108667,16,(.group 8 291 false)⟩))
(.branch 108699
(.leaf ⟨108683,16,(.group 8 292 false)⟩)
(.leaf ⟨108699,16,(.group 8 293 false)⟩)))
(.branch 108747
(.branch 108731
(.leaf ⟨108715,16,(.group 8 294 false)⟩)
(.leaf ⟨108731,16,(.group 8 295 false)⟩))
(.branch 108763
(.leaf ⟨108747,16,(.group 8 296 false)⟩)
(.leaf ⟨108763,16,(.group 8 297 false)⟩))))))
(.branch 109035
(.branch 108907
(.branch 108843
(.branch 108811
(.branch 108795
(.leaf ⟨108779,16,(.group 8 298 false)⟩)
(.leaf ⟨108795,16,(.group 8 299 false)⟩))
(.branch 108827
(.leaf ⟨108811,16,(.group 8 300 false)⟩)
(.leaf ⟨108827,16,(.group 8 301 false)⟩)))
(.branch 108875
(.branch 108859
(.leaf ⟨108843,16,(.group 8 302 false)⟩)
(.leaf ⟨108859,16,(.group 8 303 false)⟩))
(.branch 108891
(.leaf ⟨108875,16,(.group 8 304 false)⟩)
(.leaf ⟨108891,16,(.group 8 305 false)⟩))))
(.branch 108971
(.branch 108939
(.branch 108923
(.leaf ⟨108907,16,(.group 8 306 false)⟩)
(.leaf ⟨108923,16,(.group 8 307 false)⟩))
(.branch 108955
(.leaf ⟨108939,16,(.group 8 308 false)⟩)
(.leaf ⟨108955,16,(.group 8 309 false)⟩)))
(.branch 109003
(.branch 108987
(.leaf ⟨108971,16,(.group 8 310 false)⟩)
(.leaf ⟨108987,16,(.group 8 311 false)⟩))
(.branch 109019
(.leaf ⟨109003,16,(.group 8 312 false)⟩)
(.leaf ⟨109019,16,(.group 8 313 false)⟩)))))
(.branch 109163
(.branch 109099
(.branch 109067
(.branch 109051
(.leaf ⟨109035,16,(.group 8 314 false)⟩)
(.leaf ⟨109051,16,(.group 8 315 false)⟩))
(.branch 109083
(.leaf ⟨109067,16,(.group 8 316 false)⟩)
(.leaf ⟨109083,16,(.group 8 317 false)⟩)))
(.branch 109131
(.branch 109115
(.leaf ⟨109099,16,(.group 8 318 false)⟩)
(.leaf ⟨109115,16,(.group 8 319 false)⟩))
(.branch 109147
(.leaf ⟨109131,16,(.group 8 320 false)⟩)
(.leaf ⟨109147,16,(.group 8 321 false)⟩))))
(.branch 109227
(.branch 109195
(.branch 109179
(.leaf ⟨109163,16,(.group 8 322 false)⟩)
(.leaf ⟨109179,16,(.group 9 259 false)⟩))
(.branch 109211
(.leaf ⟨109195,16,(.group 9 260 false)⟩)
(.leaf ⟨109211,16,(.group 9 261 false)⟩)))
(.branch 109259
(.branch 109243
(.leaf ⟨109227,16,(.group 9 262 false)⟩)
(.leaf ⟨109243,16,(.group 9 263 false)⟩))
(.branch 109275
(.leaf ⟨109259,16,(.group 9 264 false)⟩)
(.leaf ⟨109275,16,(.group 9 265 false)⟩)))))))

theorem tree111_checked : tree111.check 108267 109291 = true := by decide +kernel

def tree112 : Tree := (.branch 109805
(.branch 109547
(.branch 109419
(.branch 109355
(.branch 109323
(.branch 109307
(.leaf ⟨109291,16,(.group 9 266 false)⟩)
(.leaf ⟨109307,16,(.group 9 267 false)⟩))
(.branch 109339
(.leaf ⟨109323,16,(.group 9 268 false)⟩)
(.leaf ⟨109339,16,(.group 9 269 false)⟩)))
(.branch 109387
(.branch 109371
(.leaf ⟨109355,16,(.group 9 270 false)⟩)
(.leaf ⟨109371,16,(.group 9 271 false)⟩))
(.branch 109403
(.leaf ⟨109387,16,(.group 9 272 false)⟩)
(.leaf ⟨109403,16,(.group 9 273 false)⟩))))
(.branch 109483
(.branch 109451
(.branch 109435
(.leaf ⟨109419,16,(.group 9 274 false)⟩)
(.leaf ⟨109435,16,(.group 9 275 false)⟩))
(.branch 109467
(.leaf ⟨109451,16,(.group 9 276 false)⟩)
(.leaf ⟨109467,16,(.group 9 277 false)⟩)))
(.branch 109515
(.branch 109499
(.leaf ⟨109483,16,(.group 9 278 false)⟩)
(.leaf ⟨109499,16,(.group 9 279 false)⟩))
(.branch 109531
(.leaf ⟨109515,16,(.group 9 280 false)⟩)
(.leaf ⟨109531,16,(.group 9 281 false)⟩)))))
(.branch 109675
(.branch 109611
(.branch 109579
(.branch 109563
(.leaf ⟨109547,16,(.group 9 282 false)⟩)
(.leaf ⟨109563,16,(.group 9 283 false)⟩))
(.branch 109595
(.leaf ⟨109579,16,(.group 9 284 false)⟩)
(.leaf ⟨109595,16,(.group 9 285 false)⟩)))
(.branch 109643
(.branch 109627
(.leaf ⟨109611,16,(.group 9 286 false)⟩)
(.leaf ⟨109627,16,(.group 9 287 false)⟩))
(.branch 109659
(.leaf ⟨109643,16,(.group 9 288 false)⟩)
(.leaf ⟨109659,16,(.group 9 289 false)⟩))))
(.branch 109739
(.branch 109707
(.branch 109691
(.leaf ⟨109675,16,(.group 9 290 false)⟩)
(.leaf ⟨109691,16,(.group 9 291 false)⟩))
(.branch 109723
(.leaf ⟨109707,16,(.group 9 292 false)⟩)
(.leaf ⟨109723,16,(.group 9 293 false)⟩)))
(.branch 109771
(.branch 109755
(.leaf ⟨109739,16,(.group 9 294 false)⟩)
(.leaf ⟨109755,16,(.group 9 295 false)⟩))
(.branch 109788
(.leaf ⟨109771,17,(.group 0 570 false)⟩)
(.leaf ⟨109788,17,(.group 0 571 false)⟩))))))
(.branch 110077
(.branch 109941
(.branch 109873
(.branch 109839
(.branch 109822
(.leaf ⟨109805,17,(.group 0 572 false)⟩)
(.leaf ⟨109822,17,(.group 0 573 false)⟩))
(.branch 109856
(.leaf ⟨109839,17,(.group 0 574 false)⟩)
(.leaf ⟨109856,17,(.group 0 575 false)⟩)))
(.branch 109907
(.branch 109890
(.leaf ⟨109873,17,(.group 0 576 false)⟩)
(.leaf ⟨109890,17,(.group 0 577 false)⟩))
(.branch 109924
(.leaf ⟨109907,17,(.group 0 578 false)⟩)
(.leaf ⟨109924,17,(.group 0 579 false)⟩))))
(.branch 110009
(.branch 109975
(.branch 109958
(.leaf ⟨109941,17,(.group 0 580 false)⟩)
(.leaf ⟨109958,17,(.group 0 581 false)⟩))
(.branch 109992
(.leaf ⟨109975,17,(.group 0 582 false)⟩)
(.leaf ⟨109992,17,(.group 0 583 false)⟩)))
(.branch 110043
(.branch 110026
(.leaf ⟨110009,17,(.group 0 584 false)⟩)
(.leaf ⟨110026,17,(.group 0 585 false)⟩))
(.branch 110060
(.leaf ⟨110043,17,(.group 0 586 false)⟩)
(.leaf ⟨110060,17,(.group 0 587 false)⟩)))))
(.branch 110213
(.branch 110145
(.branch 110111
(.branch 110094
(.leaf ⟨110077,17,(.group 0 588 false)⟩)
(.leaf ⟨110094,17,(.group 0 589 false)⟩))
(.branch 110128
(.leaf ⟨110111,17,(.group 0 590 false)⟩)
(.leaf ⟨110128,17,(.group 0 591 false)⟩)))
(.branch 110179
(.branch 110162
(.leaf ⟨110145,17,(.group 0 592 false)⟩)
(.leaf ⟨110162,17,(.group 0 593 false)⟩))
(.branch 110196
(.leaf ⟨110179,17,(.group 0 594 false)⟩)
(.leaf ⟨110196,17,(.group 0 595 false)⟩))))
(.branch 110281
(.branch 110247
(.branch 110230
(.leaf ⟨110213,17,(.group 0 596 false)⟩)
(.leaf ⟨110230,17,(.group 0 597 false)⟩))
(.branch 110264
(.leaf ⟨110247,17,(.group 0 598 false)⟩)
(.leaf ⟨110264,17,(.group 0 599 false)⟩)))
(.branch 110315
(.branch 110298
(.leaf ⟨110281,17,(.group 0 600 false)⟩)
(.leaf ⟨110298,17,(.group 0 601 false)⟩))
(.branch 110332
(.leaf ⟨110315,17,(.group 0 602 false)⟩)
(.leaf ⟨110332,17,(.group 0 603 false)⟩)))))))

theorem tree112_checked : tree112.check 109291 110349 = true := by decide +kernel

def tree113 : Tree := (.branch 110893
(.branch 110621
(.branch 110485
(.branch 110417
(.branch 110383
(.branch 110366
(.leaf ⟨110349,17,(.group 0 604 false)⟩)
(.leaf ⟨110366,17,(.group 0 605 false)⟩))
(.branch 110400
(.leaf ⟨110383,17,(.group 0 606 false)⟩)
(.leaf ⟨110400,17,(.group 0 607 false)⟩)))
(.branch 110451
(.branch 110434
(.leaf ⟨110417,17,(.group 0 608 false)⟩)
(.leaf ⟨110434,17,(.group 0 609 false)⟩))
(.branch 110468
(.leaf ⟨110451,17,(.group 0 610 false)⟩)
(.leaf ⟨110468,17,(.group 0 611 false)⟩))))
(.branch 110553
(.branch 110519
(.branch 110502
(.leaf ⟨110485,17,(.group 0 612 false)⟩)
(.leaf ⟨110502,17,(.group 0 613 false)⟩))
(.branch 110536
(.leaf ⟨110519,17,(.group 0 614 false)⟩)
(.leaf ⟨110536,17,(.group 0 615 false)⟩)))
(.branch 110587
(.branch 110570
(.leaf ⟨110553,17,(.group 0 616 false)⟩)
(.leaf ⟨110570,17,(.group 0 617 false)⟩))
(.branch 110604
(.leaf ⟨110587,17,(.group 0 618 false)⟩)
(.leaf ⟨110604,17,(.group 0 619 false)⟩)))))
(.branch 110757
(.branch 110689
(.branch 110655
(.branch 110638
(.leaf ⟨110621,17,(.group 0 620 false)⟩)
(.leaf ⟨110638,17,(.group 0 621 false)⟩))
(.branch 110672
(.leaf ⟨110655,17,(.group 0 622 false)⟩)
(.leaf ⟨110672,17,(.group 0 623 false)⟩)))
(.branch 110723
(.branch 110706
(.leaf ⟨110689,17,(.group 0 624 false)⟩)
(.leaf ⟨110706,17,(.group 0 625 false)⟩))
(.branch 110740
(.leaf ⟨110723,17,(.group 0 626 false)⟩)
(.leaf ⟨110740,17,(.group 0 627 false)⟩))))
(.branch 110825
(.branch 110791
(.branch 110774
(.leaf ⟨110757,17,(.group 0 628 false)⟩)
(.leaf ⟨110774,17,(.group 0 629 false)⟩))
(.branch 110808
(.leaf ⟨110791,17,(.group 0 630 false)⟩)
(.leaf ⟨110808,17,(.group 0 631 false)⟩)))
(.branch 110859
(.branch 110842
(.leaf ⟨110825,17,(.group 0 632 false)⟩)
(.leaf ⟨110842,17,(.group 0 633 false)⟩))
(.branch 110876
(.leaf ⟨110859,17,(.group 0 634 false)⟩)
(.leaf ⟨110876,17,(.group 0 635 false)⟩))))))
(.branch 111165
(.branch 111029
(.branch 110961
(.branch 110927
(.branch 110910
(.leaf ⟨110893,17,(.group 0 636 false)⟩)
(.leaf ⟨110910,17,(.group 0 637 false)⟩))
(.branch 110944
(.leaf ⟨110927,17,(.group 0 638 false)⟩)
(.leaf ⟨110944,17,(.group 0 639 false)⟩)))
(.branch 110995
(.branch 110978
(.leaf ⟨110961,17,(.group 0 640 false)⟩)
(.leaf ⟨110978,17,(.group 0 641 false)⟩))
(.branch 111012
(.leaf ⟨110995,17,(.group 0 642 false)⟩)
(.leaf ⟨111012,17,(.group 0 643 false)⟩))))
(.branch 111097
(.branch 111063
(.branch 111046
(.leaf ⟨111029,17,(.group 0 644 false)⟩)
(.leaf ⟨111046,17,(.group 0 645 false)⟩))
(.branch 111080
(.leaf ⟨111063,17,(.group 0 646 false)⟩)
(.leaf ⟨111080,17,(.group 0 647 false)⟩)))
(.branch 111131
(.branch 111114
(.leaf ⟨111097,17,(.group 0 648 false)⟩)
(.leaf ⟨111114,17,(.group 0 649 false)⟩))
(.branch 111148
(.leaf ⟨111131,17,(.group 0 650 false)⟩)
(.leaf ⟨111148,17,(.group 0 651 false)⟩)))))
(.branch 111301
(.branch 111233
(.branch 111199
(.branch 111182
(.leaf ⟨111165,17,(.group 0 652 false)⟩)
(.leaf ⟨111182,17,(.group 0 653 false)⟩))
(.branch 111216
(.leaf ⟨111199,17,(.group 0 654 false)⟩)
(.leaf ⟨111216,17,(.group 0 655 false)⟩)))
(.branch 111267
(.branch 111250
(.leaf ⟨111233,17,(.group 0 656 false)⟩)
(.leaf ⟨111250,17,(.group 0 657 false)⟩))
(.branch 111284
(.leaf ⟨111267,17,(.group 0 658 false)⟩)
(.leaf ⟨111284,17,(.group 0 659 false)⟩))))
(.branch 111369
(.branch 111335
(.branch 111318
(.leaf ⟨111301,17,(.group 0 660 false)⟩)
(.leaf ⟨111318,17,(.group 0 661 false)⟩))
(.branch 111352
(.leaf ⟨111335,17,(.group 0 662 false)⟩)
(.leaf ⟨111352,17,(.group 0 663 false)⟩)))
(.branch 111403
(.branch 111386
(.leaf ⟨111369,17,(.group 0 664 false)⟩)
(.leaf ⟨111386,17,(.group 0 665 false)⟩))
(.branch 111420
(.leaf ⟨111403,17,(.group 0 666 false)⟩)
(.leaf ⟨111420,17,(.group 0 667 false)⟩)))))))

theorem tree113_checked : tree113.check 110349 111437 = true := by decide +kernel

def tree114 : Tree := (.branch 111981
(.branch 111709
(.branch 111573
(.branch 111505
(.branch 111471
(.branch 111454
(.leaf ⟨111437,17,(.group 0 668 false)⟩)
(.leaf ⟨111454,17,(.group 0 669 false)⟩))
(.branch 111488
(.leaf ⟨111471,17,(.group 0 670 false)⟩)
(.leaf ⟨111488,17,(.group 0 671 false)⟩)))
(.branch 111539
(.branch 111522
(.leaf ⟨111505,17,(.group 0 672 false)⟩)
(.leaf ⟨111522,17,(.group 0 673 false)⟩))
(.branch 111556
(.leaf ⟨111539,17,(.group 0 674 false)⟩)
(.leaf ⟨111556,17,(.group 0 675 false)⟩))))
(.branch 111641
(.branch 111607
(.branch 111590
(.leaf ⟨111573,17,(.group 0 676 false)⟩)
(.leaf ⟨111590,17,(.group 0 677 false)⟩))
(.branch 111624
(.leaf ⟨111607,17,(.group 0 678 false)⟩)
(.leaf ⟨111624,17,(.group 0 679 false)⟩)))
(.branch 111675
(.branch 111658
(.leaf ⟨111641,17,(.group 0 680 false)⟩)
(.leaf ⟨111658,17,(.group 0 681 false)⟩))
(.branch 111692
(.leaf ⟨111675,17,(.group 0 682 false)⟩)
(.leaf ⟨111692,17,(.group 0 683 false)⟩)))))
(.branch 111845
(.branch 111777
(.branch 111743
(.branch 111726
(.leaf ⟨111709,17,(.group 0 684 false)⟩)
(.leaf ⟨111726,17,(.group 0 685 false)⟩))
(.branch 111760
(.leaf ⟨111743,17,(.group 0 686 false)⟩)
(.leaf ⟨111760,17,(.group 0 687 false)⟩)))
(.branch 111811
(.branch 111794
(.leaf ⟨111777,17,(.group 0 688 false)⟩)
(.leaf ⟨111794,17,(.group 0 689 false)⟩))
(.branch 111828
(.leaf ⟨111811,17,(.group 0 690 false)⟩)
(.leaf ⟨111828,17,(.group 0 691 false)⟩))))
(.branch 111913
(.branch 111879
(.branch 111862
(.leaf ⟨111845,17,(.group 0 692 false)⟩)
(.leaf ⟨111862,17,(.group 0 693 false)⟩))
(.branch 111896
(.leaf ⟨111879,17,(.group 0 694 false)⟩)
(.leaf ⟨111896,17,(.group 0 695 false)⟩)))
(.branch 111947
(.branch 111930
(.leaf ⟨111913,17,(.group 0 696 false)⟩)
(.leaf ⟨111930,17,(.group 0 697 false)⟩))
(.branch 111964
(.leaf ⟨111947,17,(.group 0 698 false)⟩)
(.leaf ⟨111964,17,(.group 0 699 false)⟩))))))
(.branch 112253
(.branch 112117
(.branch 112049
(.branch 112015
(.branch 111998
(.leaf ⟨111981,17,(.group 0 700 false)⟩)
(.leaf ⟨111998,17,(.group 0 701 false)⟩))
(.branch 112032
(.leaf ⟨112015,17,(.group 0 702 false)⟩)
(.leaf ⟨112032,17,(.group 0 703 false)⟩)))
(.branch 112083
(.branch 112066
(.leaf ⟨112049,17,(.group 0 704 false)⟩)
(.leaf ⟨112066,17,(.group 0 705 false)⟩))
(.branch 112100
(.leaf ⟨112083,17,(.group 0 706 false)⟩)
(.leaf ⟨112100,17,(.group 0 707 false)⟩))))
(.branch 112185
(.branch 112151
(.branch 112134
(.leaf ⟨112117,17,(.group 0 708 false)⟩)
(.leaf ⟨112134,17,(.group 0 709 false)⟩))
(.branch 112168
(.leaf ⟨112151,17,(.group 0 710 false)⟩)
(.leaf ⟨112168,17,(.group 0 711 false)⟩)))
(.branch 112219
(.branch 112202
(.leaf ⟨112185,17,(.group 0 712 false)⟩)
(.leaf ⟨112202,17,(.group 0 713 false)⟩))
(.branch 112236
(.leaf ⟨112219,17,(.group 0 714 false)⟩)
(.leaf ⟨112236,17,(.group 0 715 false)⟩)))))
(.branch 112389
(.branch 112321
(.branch 112287
(.branch 112270
(.leaf ⟨112253,17,(.group 0 716 false)⟩)
(.leaf ⟨112270,17,(.group 0 717 false)⟩))
(.branch 112304
(.leaf ⟨112287,17,(.group 0 718 false)⟩)
(.leaf ⟨112304,17,(.group 0 719 false)⟩)))
(.branch 112355
(.branch 112338
(.leaf ⟨112321,17,(.group 0 720 false)⟩)
(.leaf ⟨112338,17,(.group 0 721 false)⟩))
(.branch 112372
(.leaf ⟨112355,17,(.group 0 722 false)⟩)
(.leaf ⟨112372,17,(.group 0 723 false)⟩))))
(.branch 112457
(.branch 112423
(.branch 112406
(.leaf ⟨112389,17,(.group 0 724 false)⟩)
(.leaf ⟨112406,17,(.group 0 725 false)⟩))
(.branch 112440
(.leaf ⟨112423,17,(.group 1 220 false)⟩)
(.leaf ⟨112440,17,(.group 1 221 false)⟩)))
(.branch 112491
(.branch 112474
(.leaf ⟨112457,17,(.group 1 222 false)⟩)
(.leaf ⟨112474,17,(.group 1 223 false)⟩))
(.branch 112508
(.leaf ⟨112491,17,(.group 1 224 false)⟩)
(.leaf ⟨112508,17,(.group 1 225 false)⟩)))))))

theorem tree114_checked : tree114.check 111437 112525 = true := by decide +kernel

def tree115 : Tree := (.branch 113069
(.branch 112797
(.branch 112661
(.branch 112593
(.branch 112559
(.branch 112542
(.leaf ⟨112525,17,(.group 1 226 false)⟩)
(.leaf ⟨112542,17,(.group 1 227 false)⟩))
(.branch 112576
(.leaf ⟨112559,17,(.group 1 228 false)⟩)
(.leaf ⟨112576,17,(.group 1 229 false)⟩)))
(.branch 112627
(.branch 112610
(.leaf ⟨112593,17,(.group 1 230 false)⟩)
(.leaf ⟨112610,17,(.group 1 231 false)⟩))
(.branch 112644
(.leaf ⟨112627,17,(.group 1 232 false)⟩)
(.leaf ⟨112644,17,(.group 1 233 false)⟩))))
(.branch 112729
(.branch 112695
(.branch 112678
(.leaf ⟨112661,17,(.group 1 234 false)⟩)
(.leaf ⟨112678,17,(.group 1 235 false)⟩))
(.branch 112712
(.leaf ⟨112695,17,(.group 1 236 false)⟩)
(.leaf ⟨112712,17,(.group 1 237 false)⟩)))
(.branch 112763
(.branch 112746
(.leaf ⟨112729,17,(.group 1 238 false)⟩)
(.leaf ⟨112746,17,(.group 1 239 false)⟩))
(.branch 112780
(.leaf ⟨112763,17,(.group 1 240 false)⟩)
(.leaf ⟨112780,17,(.group 1 241 false)⟩)))))
(.branch 112933
(.branch 112865
(.branch 112831
(.branch 112814
(.leaf ⟨112797,17,(.group 1 242 false)⟩)
(.leaf ⟨112814,17,(.group 1 243 false)⟩))
(.branch 112848
(.leaf ⟨112831,17,(.group 1 244 false)⟩)
(.leaf ⟨112848,17,(.group 1 245 false)⟩)))
(.branch 112899
(.branch 112882
(.leaf ⟨112865,17,(.group 1 246 false)⟩)
(.leaf ⟨112882,17,(.group 1 247 false)⟩))
(.branch 112916
(.leaf ⟨112899,17,(.group 1 248 false)⟩)
(.leaf ⟨112916,17,(.group 1 249 false)⟩))))
(.branch 113001
(.branch 112967
(.branch 112950
(.leaf ⟨112933,17,(.group 1 250 false)⟩)
(.leaf ⟨112950,17,(.group 1 251 false)⟩))
(.branch 112984
(.leaf ⟨112967,17,(.group 1 252 false)⟩)
(.leaf ⟨112984,17,(.group 1 253 false)⟩)))
(.branch 113035
(.branch 113018
(.leaf ⟨113001,17,(.group 1 254 false)⟩)
(.leaf ⟨113018,17,(.group 1 255 false)⟩))
(.branch 113052
(.leaf ⟨113035,17,(.group 1 256 false)⟩)
(.leaf ⟨113052,17,(.group 1 257 false)⟩))))))
(.branch 113341
(.branch 113205
(.branch 113137
(.branch 113103
(.branch 113086
(.leaf ⟨113069,17,(.group 1 258 false)⟩)
(.leaf ⟨113086,17,(.group 1 259 false)⟩))
(.branch 113120
(.leaf ⟨113103,17,(.group 1 260 false)⟩)
(.leaf ⟨113120,17,(.group 1 261 false)⟩)))
(.branch 113171
(.branch 113154
(.leaf ⟨113137,17,(.group 1 262 false)⟩)
(.leaf ⟨113154,17,(.group 1 263 false)⟩))
(.branch 113188
(.leaf ⟨113171,17,(.group 1 264 false)⟩)
(.leaf ⟨113188,17,(.group 1 265 false)⟩))))
(.branch 113273
(.branch 113239
(.branch 113222
(.leaf ⟨113205,17,(.group 1 266 false)⟩)
(.leaf ⟨113222,17,(.group 1 267 false)⟩))
(.branch 113256
(.leaf ⟨113239,17,(.group 1 268 false)⟩)
(.leaf ⟨113256,17,(.group 1 269 false)⟩)))
(.branch 113307
(.branch 113290
(.leaf ⟨113273,17,(.group 1 270 false)⟩)
(.leaf ⟨113290,17,(.group 1 271 false)⟩))
(.branch 113324
(.leaf ⟨113307,17,(.group 1 272 false)⟩)
(.leaf ⟨113324,17,(.group 1 273 false)⟩)))))
(.branch 113477
(.branch 113409
(.branch 113375
(.branch 113358
(.leaf ⟨113341,17,(.group 1 274 false)⟩)
(.leaf ⟨113358,17,(.group 1 275 false)⟩))
(.branch 113392
(.leaf ⟨113375,17,(.group 1 276 false)⟩)
(.leaf ⟨113392,17,(.group 1 277 false)⟩)))
(.branch 113443
(.branch 113426
(.leaf ⟨113409,17,(.group 1 278 false)⟩)
(.leaf ⟨113426,17,(.group 1 279 false)⟩))
(.branch 113460
(.leaf ⟨113443,17,(.group 1 280 false)⟩)
(.leaf ⟨113460,17,(.group 1 281 false)⟩))))
(.branch 113545
(.branch 113511
(.branch 113494
(.leaf ⟨113477,17,(.group 1 282 false)⟩)
(.leaf ⟨113494,17,(.group 1 283 false)⟩))
(.branch 113528
(.leaf ⟨113511,17,(.group 1 284 false)⟩)
(.leaf ⟨113528,17,(.group 1 285 false)⟩)))
(.branch 113579
(.branch 113562
(.leaf ⟨113545,17,(.group 2 220 false)⟩)
(.leaf ⟨113562,17,(.group 2 221 false)⟩))
(.branch 113596
(.leaf ⟨113579,17,(.group 2 222 false)⟩)
(.leaf ⟨113596,17,(.group 2 223 false)⟩)))))))

theorem tree115_checked : tree115.check 112525 113613 = true := by decide +kernel

def tree116 : Tree := (.branch 114157
(.branch 113885
(.branch 113749
(.branch 113681
(.branch 113647
(.branch 113630
(.leaf ⟨113613,17,(.group 2 224 false)⟩)
(.leaf ⟨113630,17,(.group 2 225 false)⟩))
(.branch 113664
(.leaf ⟨113647,17,(.group 2 226 false)⟩)
(.leaf ⟨113664,17,(.group 2 227 false)⟩)))
(.branch 113715
(.branch 113698
(.leaf ⟨113681,17,(.group 2 228 false)⟩)
(.leaf ⟨113698,17,(.group 2 229 false)⟩))
(.branch 113732
(.leaf ⟨113715,17,(.group 2 230 false)⟩)
(.leaf ⟨113732,17,(.group 2 231 false)⟩))))
(.branch 113817
(.branch 113783
(.branch 113766
(.leaf ⟨113749,17,(.group 2 232 false)⟩)
(.leaf ⟨113766,17,(.group 2 233 false)⟩))
(.branch 113800
(.leaf ⟨113783,17,(.group 2 234 false)⟩)
(.leaf ⟨113800,17,(.group 2 235 false)⟩)))
(.branch 113851
(.branch 113834
(.leaf ⟨113817,17,(.group 2 236 false)⟩)
(.leaf ⟨113834,17,(.group 2 237 false)⟩))
(.branch 113868
(.leaf ⟨113851,17,(.group 2 238 false)⟩)
(.leaf ⟨113868,17,(.group 2 239 false)⟩)))))
(.branch 114021
(.branch 113953
(.branch 113919
(.branch 113902
(.leaf ⟨113885,17,(.group 2 240 false)⟩)
(.leaf ⟨113902,17,(.group 2 241 false)⟩))
(.branch 113936
(.leaf ⟨113919,17,(.group 2 242 false)⟩)
(.leaf ⟨113936,17,(.group 2 243 false)⟩)))
(.branch 113987
(.branch 113970
(.leaf ⟨113953,17,(.group 2 244 false)⟩)
(.leaf ⟨113970,17,(.group 2 245 false)⟩))
(.branch 114004
(.leaf ⟨113987,17,(.group 2 246 false)⟩)
(.leaf ⟨114004,17,(.group 2 247 false)⟩))))
(.branch 114089
(.branch 114055
(.branch 114038
(.leaf ⟨114021,17,(.group 2 248 false)⟩)
(.leaf ⟨114038,17,(.group 2 249 false)⟩))
(.branch 114072
(.leaf ⟨114055,17,(.group 2 250 false)⟩)
(.leaf ⟨114072,17,(.group 2 251 false)⟩)))
(.branch 114123
(.branch 114106
(.leaf ⟨114089,17,(.group 2 252 false)⟩)
(.leaf ⟨114106,17,(.group 2 253 false)⟩))
(.branch 114140
(.leaf ⟨114123,17,(.group 2 254 false)⟩)
(.leaf ⟨114140,17,(.group 2 255 false)⟩))))))
(.branch 114429
(.branch 114293
(.branch 114225
(.branch 114191
(.branch 114174
(.leaf ⟨114157,17,(.group 2 256 false)⟩)
(.leaf ⟨114174,17,(.group 2 257 false)⟩))
(.branch 114208
(.leaf ⟨114191,17,(.group 2 258 false)⟩)
(.leaf ⟨114208,17,(.group 2 259 false)⟩)))
(.branch 114259
(.branch 114242
(.leaf ⟨114225,17,(.group 2 260 false)⟩)
(.leaf ⟨114242,17,(.group 2 261 false)⟩))
(.branch 114276
(.leaf ⟨114259,17,(.group 2 262 false)⟩)
(.leaf ⟨114276,17,(.group 2 263 false)⟩))))
(.branch 114361
(.branch 114327
(.branch 114310
(.leaf ⟨114293,17,(.group 2 264 false)⟩)
(.leaf ⟨114310,17,(.group 2 265 false)⟩))
(.branch 114344
(.leaf ⟨114327,17,(.group 2 266 false)⟩)
(.leaf ⟨114344,17,(.group 2 267 false)⟩)))
(.branch 114395
(.branch 114378
(.leaf ⟨114361,17,(.group 2 268 false)⟩)
(.leaf ⟨114378,17,(.group 2 269 false)⟩))
(.branch 114412
(.leaf ⟨114395,17,(.group 2 270 false)⟩)
(.leaf ⟨114412,17,(.group 2 271 false)⟩)))))
(.branch 114565
(.branch 114497
(.branch 114463
(.branch 114446
(.leaf ⟨114429,17,(.group 2 272 false)⟩)
(.leaf ⟨114446,17,(.group 2 273 false)⟩))
(.branch 114480
(.leaf ⟨114463,17,(.group 2 274 false)⟩)
(.leaf ⟨114480,17,(.group 2 275 false)⟩)))
(.branch 114531
(.branch 114514
(.leaf ⟨114497,17,(.group 2 276 false)⟩)
(.leaf ⟨114514,17,(.group 2 277 false)⟩))
(.branch 114548
(.leaf ⟨114531,17,(.group 2 278 false)⟩)
(.leaf ⟨114548,17,(.group 2 279 false)⟩))))
(.branch 114633
(.branch 114599
(.branch 114582
(.leaf ⟨114565,17,(.group 2 280 false)⟩)
(.leaf ⟨114582,17,(.group 2 281 false)⟩))
(.branch 114616
(.leaf ⟨114599,17,(.group 2 282 false)⟩)
(.leaf ⟨114616,17,(.group 2 283 false)⟩)))
(.branch 114667
(.branch 114650
(.leaf ⟨114633,17,(.group 2 284 false)⟩)
(.leaf ⟨114650,17,(.group 2 285 false)⟩))
(.branch 114684
(.leaf ⟨114667,17,(.group 3 220 false)⟩)
(.leaf ⟨114684,17,(.group 3 221 false)⟩)))))))

theorem tree116_checked : tree116.check 113613 114701 = true := by decide +kernel

def tree117 : Tree := (.branch 115245
(.branch 114973
(.branch 114837
(.branch 114769
(.branch 114735
(.branch 114718
(.leaf ⟨114701,17,(.group 3 222 false)⟩)
(.leaf ⟨114718,17,(.group 3 223 false)⟩))
(.branch 114752
(.leaf ⟨114735,17,(.group 3 224 false)⟩)
(.leaf ⟨114752,17,(.group 3 225 false)⟩)))
(.branch 114803
(.branch 114786
(.leaf ⟨114769,17,(.group 3 226 false)⟩)
(.leaf ⟨114786,17,(.group 3 227 false)⟩))
(.branch 114820
(.leaf ⟨114803,17,(.group 3 228 false)⟩)
(.leaf ⟨114820,17,(.group 3 229 false)⟩))))
(.branch 114905
(.branch 114871
(.branch 114854
(.leaf ⟨114837,17,(.group 3 230 false)⟩)
(.leaf ⟨114854,17,(.group 3 231 false)⟩))
(.branch 114888
(.leaf ⟨114871,17,(.group 3 232 false)⟩)
(.leaf ⟨114888,17,(.group 3 233 false)⟩)))
(.branch 114939
(.branch 114922
(.leaf ⟨114905,17,(.group 3 234 false)⟩)
(.leaf ⟨114922,17,(.group 3 235 false)⟩))
(.branch 114956
(.leaf ⟨114939,17,(.group 3 236 false)⟩)
(.leaf ⟨114956,17,(.group 3 237 false)⟩)))))
(.branch 115109
(.branch 115041
(.branch 115007
(.branch 114990
(.leaf ⟨114973,17,(.group 3 238 false)⟩)
(.leaf ⟨114990,17,(.group 3 239 false)⟩))
(.branch 115024
(.leaf ⟨115007,17,(.group 3 240 false)⟩)
(.leaf ⟨115024,17,(.group 3 241 false)⟩)))
(.branch 115075
(.branch 115058
(.leaf ⟨115041,17,(.group 3 242 false)⟩)
(.leaf ⟨115058,17,(.group 3 243 false)⟩))
(.branch 115092
(.leaf ⟨115075,17,(.group 3 244 false)⟩)
(.leaf ⟨115092,17,(.group 3 245 false)⟩))))
(.branch 115177
(.branch 115143
(.branch 115126
(.leaf ⟨115109,17,(.group 3 246 false)⟩)
(.leaf ⟨115126,17,(.group 3 247 false)⟩))
(.branch 115160
(.leaf ⟨115143,17,(.group 3 248 false)⟩)
(.leaf ⟨115160,17,(.group 3 249 false)⟩)))
(.branch 115211
(.branch 115194
(.leaf ⟨115177,17,(.group 3 250 false)⟩)
(.leaf ⟨115194,17,(.group 3 251 false)⟩))
(.branch 115228
(.leaf ⟨115211,17,(.group 3 252 false)⟩)
(.leaf ⟨115228,17,(.group 3 253 false)⟩))))))
(.branch 115517
(.branch 115381
(.branch 115313
(.branch 115279
(.branch 115262
(.leaf ⟨115245,17,(.group 3 254 false)⟩)
(.leaf ⟨115262,17,(.group 3 255 false)⟩))
(.branch 115296
(.leaf ⟨115279,17,(.group 3 256 false)⟩)
(.leaf ⟨115296,17,(.group 3 257 false)⟩)))
(.branch 115347
(.branch 115330
(.leaf ⟨115313,17,(.group 3 258 false)⟩)
(.leaf ⟨115330,17,(.group 3 259 false)⟩))
(.branch 115364
(.leaf ⟨115347,17,(.group 3 260 false)⟩)
(.leaf ⟨115364,17,(.group 3 261 false)⟩))))
(.branch 115449
(.branch 115415
(.branch 115398
(.leaf ⟨115381,17,(.group 3 262 false)⟩)
(.leaf ⟨115398,17,(.group 3 263 false)⟩))
(.branch 115432
(.leaf ⟨115415,17,(.group 3 264 false)⟩)
(.leaf ⟨115432,17,(.group 3 265 false)⟩)))
(.branch 115483
(.branch 115466
(.leaf ⟨115449,17,(.group 3 266 false)⟩)
(.leaf ⟨115466,17,(.group 3 267 false)⟩))
(.branch 115500
(.leaf ⟨115483,17,(.group 3 268 false)⟩)
(.leaf ⟨115500,17,(.group 3 269 false)⟩)))))
(.branch 115653
(.branch 115585
(.branch 115551
(.branch 115534
(.leaf ⟨115517,17,(.group 3 270 false)⟩)
(.leaf ⟨115534,17,(.group 3 271 false)⟩))
(.branch 115568
(.leaf ⟨115551,17,(.group 3 272 false)⟩)
(.leaf ⟨115568,17,(.group 3 273 false)⟩)))
(.branch 115619
(.branch 115602
(.leaf ⟨115585,17,(.group 3 274 false)⟩)
(.leaf ⟨115602,17,(.group 3 275 false)⟩))
(.branch 115636
(.leaf ⟨115619,17,(.group 3 276 false)⟩)
(.leaf ⟨115636,17,(.group 3 277 false)⟩))))
(.branch 115721
(.branch 115687
(.branch 115670
(.leaf ⟨115653,17,(.group 3 278 false)⟩)
(.leaf ⟨115670,17,(.group 3 279 false)⟩))
(.branch 115704
(.leaf ⟨115687,17,(.group 3 280 false)⟩)
(.leaf ⟨115704,17,(.group 3 281 false)⟩)))
(.branch 115755
(.branch 115738
(.leaf ⟨115721,17,(.group 3 282 false)⟩)
(.leaf ⟨115738,17,(.group 3 283 false)⟩))
(.branch 115772
(.leaf ⟨115755,17,(.group 3 284 false)⟩)
(.leaf ⟨115772,17,(.group 3 285 false)⟩)))))))

theorem tree117_checked : tree117.check 114701 115789 = true := by decide +kernel

def tree118 : Tree := (.branch 116333
(.branch 116061
(.branch 115925
(.branch 115857
(.branch 115823
(.branch 115806
(.leaf ⟨115789,17,(.group 4 220 false)⟩)
(.leaf ⟨115806,17,(.group 4 221 false)⟩))
(.branch 115840
(.leaf ⟨115823,17,(.group 4 222 false)⟩)
(.leaf ⟨115840,17,(.group 4 223 false)⟩)))
(.branch 115891
(.branch 115874
(.leaf ⟨115857,17,(.group 4 224 false)⟩)
(.leaf ⟨115874,17,(.group 4 225 false)⟩))
(.branch 115908
(.leaf ⟨115891,17,(.group 4 226 false)⟩)
(.leaf ⟨115908,17,(.group 4 227 false)⟩))))
(.branch 115993
(.branch 115959
(.branch 115942
(.leaf ⟨115925,17,(.group 4 228 false)⟩)
(.leaf ⟨115942,17,(.group 4 229 false)⟩))
(.branch 115976
(.leaf ⟨115959,17,(.group 4 230 false)⟩)
(.leaf ⟨115976,17,(.group 4 231 false)⟩)))
(.branch 116027
(.branch 116010
(.leaf ⟨115993,17,(.group 4 232 false)⟩)
(.leaf ⟨116010,17,(.group 4 233 false)⟩))
(.branch 116044
(.leaf ⟨116027,17,(.group 4 234 false)⟩)
(.leaf ⟨116044,17,(.group 4 235 false)⟩)))))
(.branch 116197
(.branch 116129
(.branch 116095
(.branch 116078
(.leaf ⟨116061,17,(.group 4 236 false)⟩)
(.leaf ⟨116078,17,(.group 4 237 false)⟩))
(.branch 116112
(.leaf ⟨116095,17,(.group 4 238 false)⟩)
(.leaf ⟨116112,17,(.group 4 239 false)⟩)))
(.branch 116163
(.branch 116146
(.leaf ⟨116129,17,(.group 4 240 false)⟩)
(.leaf ⟨116146,17,(.group 4 241 false)⟩))
(.branch 116180
(.leaf ⟨116163,17,(.group 4 242 false)⟩)
(.leaf ⟨116180,17,(.group 4 243 false)⟩))))
(.branch 116265
(.branch 116231
(.branch 116214
(.leaf ⟨116197,17,(.group 4 244 false)⟩)
(.leaf ⟨116214,17,(.group 4 245 false)⟩))
(.branch 116248
(.leaf ⟨116231,17,(.group 4 246 false)⟩)
(.leaf ⟨116248,17,(.group 4 247 false)⟩)))
(.branch 116299
(.branch 116282
(.leaf ⟨116265,17,(.group 4 248 false)⟩)
(.leaf ⟨116282,17,(.group 4 249 false)⟩))
(.branch 116316
(.leaf ⟨116299,17,(.group 4 250 false)⟩)
(.leaf ⟨116316,17,(.group 4 251 false)⟩))))))
(.branch 116605
(.branch 116469
(.branch 116401
(.branch 116367
(.branch 116350
(.leaf ⟨116333,17,(.group 4 252 false)⟩)
(.leaf ⟨116350,17,(.group 4 253 false)⟩))
(.branch 116384
(.leaf ⟨116367,17,(.group 4 254 false)⟩)
(.leaf ⟨116384,17,(.group 4 255 false)⟩)))
(.branch 116435
(.branch 116418
(.leaf ⟨116401,17,(.group 4 256 false)⟩)
(.leaf ⟨116418,17,(.group 4 257 false)⟩))
(.branch 116452
(.leaf ⟨116435,17,(.group 4 258 false)⟩)
(.leaf ⟨116452,17,(.group 4 259 false)⟩))))
(.branch 116537
(.branch 116503
(.branch 116486
(.leaf ⟨116469,17,(.group 4 260 false)⟩)
(.leaf ⟨116486,17,(.group 4 261 false)⟩))
(.branch 116520
(.leaf ⟨116503,17,(.group 4 262 false)⟩)
(.leaf ⟨116520,17,(.group 4 263 false)⟩)))
(.branch 116571
(.branch 116554
(.leaf ⟨116537,17,(.group 4 264 false)⟩)
(.leaf ⟨116554,17,(.group 4 265 false)⟩))
(.branch 116588
(.leaf ⟨116571,17,(.group 4 266 false)⟩)
(.leaf ⟨116588,17,(.group 4 267 false)⟩)))))
(.branch 116741
(.branch 116673
(.branch 116639
(.branch 116622
(.leaf ⟨116605,17,(.group 4 268 false)⟩)
(.leaf ⟨116622,17,(.group 4 269 false)⟩))
(.branch 116656
(.leaf ⟨116639,17,(.group 4 270 false)⟩)
(.leaf ⟨116656,17,(.group 4 271 false)⟩)))
(.branch 116707
(.branch 116690
(.leaf ⟨116673,17,(.group 4 272 false)⟩)
(.leaf ⟨116690,17,(.group 4 273 false)⟩))
(.branch 116724
(.leaf ⟨116707,17,(.group 4 274 false)⟩)
(.leaf ⟨116724,17,(.group 4 275 false)⟩))))
(.branch 116809
(.branch 116775
(.branch 116758
(.leaf ⟨116741,17,(.group 4 276 false)⟩)
(.leaf ⟨116758,17,(.group 4 277 false)⟩))
(.branch 116792
(.leaf ⟨116775,17,(.group 4 278 false)⟩)
(.leaf ⟨116792,17,(.group 4 279 false)⟩)))
(.branch 116843
(.branch 116826
(.leaf ⟨116809,17,(.group 4 280 false)⟩)
(.leaf ⟨116826,17,(.group 4 281 false)⟩))
(.branch 116860
(.leaf ⟨116843,17,(.group 4 282 false)⟩)
(.leaf ⟨116860,17,(.group 4 283 false)⟩)))))))

theorem tree118_checked : tree118.check 115789 116877 = true := by decide +kernel

def tree119 : Tree := (.branch 117421
(.branch 117149
(.branch 117013
(.branch 116945
(.branch 116911
(.branch 116894
(.leaf ⟨116877,17,(.group 4 284 false)⟩)
(.leaf ⟨116894,17,(.group 4 285 false)⟩))
(.branch 116928
(.leaf ⟨116911,17,(.group 5 1501 false)⟩)
(.leaf ⟨116928,17,(.group 5 1502 false)⟩)))
(.branch 116979
(.branch 116962
(.leaf ⟨116945,17,(.group 5 1503 false)⟩)
(.leaf ⟨116962,17,(.group 5 1504 false)⟩))
(.branch 116996
(.leaf ⟨116979,17,(.group 5 1505 false)⟩)
(.leaf ⟨116996,17,(.group 5 1506 false)⟩))))
(.branch 117081
(.branch 117047
(.branch 117030
(.leaf ⟨117013,17,(.group 5 1507 false)⟩)
(.leaf ⟨117030,17,(.group 5 1508 false)⟩))
(.branch 117064
(.leaf ⟨117047,17,(.group 5 1509 false)⟩)
(.leaf ⟨117064,17,(.group 5 1510 false)⟩)))
(.branch 117115
(.branch 117098
(.leaf ⟨117081,17,(.group 5 1511 false)⟩)
(.leaf ⟨117098,17,(.group 5 1512 false)⟩))
(.branch 117132
(.leaf ⟨117115,17,(.group 5 1513 false)⟩)
(.leaf ⟨117132,17,(.group 5 1514 false)⟩)))))
(.branch 117285
(.branch 117217
(.branch 117183
(.branch 117166
(.leaf ⟨117149,17,(.group 5 1515 false)⟩)
(.leaf ⟨117166,17,(.group 5 1516 false)⟩))
(.branch 117200
(.leaf ⟨117183,17,(.group 5 1517 false)⟩)
(.leaf ⟨117200,17,(.group 5 1518 false)⟩)))
(.branch 117251
(.branch 117234
(.leaf ⟨117217,17,(.group 5 1519 false)⟩)
(.leaf ⟨117234,17,(.group 5 1520 false)⟩))
(.branch 117268
(.leaf ⟨117251,17,(.group 5 1521 false)⟩)
(.leaf ⟨117268,17,(.group 5 1522 false)⟩))))
(.branch 117353
(.branch 117319
(.branch 117302
(.leaf ⟨117285,17,(.group 5 1523 false)⟩)
(.leaf ⟨117302,17,(.group 5 1524 false)⟩))
(.branch 117336
(.leaf ⟨117319,17,(.group 5 1525 false)⟩)
(.leaf ⟨117336,17,(.group 5 1526 false)⟩)))
(.branch 117387
(.branch 117370
(.leaf ⟨117353,17,(.group 5 1527 false)⟩)
(.leaf ⟨117370,17,(.group 5 1528 false)⟩))
(.branch 117404
(.leaf ⟨117387,17,(.group 5 1529 false)⟩)
(.leaf ⟨117404,17,(.group 5 1530 false)⟩))))))
(.branch 117693
(.branch 117557
(.branch 117489
(.branch 117455
(.branch 117438
(.leaf ⟨117421,17,(.group 5 1531 false)⟩)
(.leaf ⟨117438,17,(.group 5 1532 false)⟩))
(.branch 117472
(.leaf ⟨117455,17,(.group 5 1533 false)⟩)
(.leaf ⟨117472,17,(.group 5 1534 false)⟩)))
(.branch 117523
(.branch 117506
(.leaf ⟨117489,17,(.group 5 1535 false)⟩)
(.leaf ⟨117506,17,(.group 5 1536 false)⟩))
(.branch 117540
(.leaf ⟨117523,17,(.group 5 1537 false)⟩)
(.leaf ⟨117540,17,(.group 5 1538 false)⟩))))
(.branch 117625
(.branch 117591
(.branch 117574
(.leaf ⟨117557,17,(.group 5 1539 false)⟩)
(.leaf ⟨117574,17,(.group 5 1540 false)⟩))
(.branch 117608
(.leaf ⟨117591,17,(.group 5 1541 false)⟩)
(.leaf ⟨117608,17,(.group 5 1542 false)⟩)))
(.branch 117659
(.branch 117642
(.leaf ⟨117625,17,(.group 5 1543 false)⟩)
(.leaf ⟨117642,17,(.group 5 1544 false)⟩))
(.branch 117676
(.leaf ⟨117659,17,(.group 5 1545 false)⟩)
(.leaf ⟨117676,17,(.group 5 1546 false)⟩)))))
(.branch 117829
(.branch 117761
(.branch 117727
(.branch 117710
(.leaf ⟨117693,17,(.group 5 1547 false)⟩)
(.leaf ⟨117710,17,(.group 5 1548 false)⟩))
(.branch 117744
(.leaf ⟨117727,17,(.group 5 1549 false)⟩)
(.leaf ⟨117744,17,(.group 5 1550 false)⟩)))
(.branch 117795
(.branch 117778
(.leaf ⟨117761,17,(.group 5 1551 false)⟩)
(.leaf ⟨117778,17,(.group 5 1552 false)⟩))
(.branch 117812
(.leaf ⟨117795,17,(.group 5 1553 false)⟩)
(.leaf ⟨117812,17,(.group 5 1554 false)⟩))))
(.branch 117897
(.branch 117863
(.branch 117846
(.leaf ⟨117829,17,(.group 5 1555 false)⟩)
(.leaf ⟨117846,17,(.group 5 1556 false)⟩))
(.branch 117880
(.leaf ⟨117863,17,(.group 5 1557 false)⟩)
(.leaf ⟨117880,17,(.group 5 1558 false)⟩)))
(.branch 117931
(.branch 117914
(.leaf ⟨117897,17,(.group 5 1559 false)⟩)
(.leaf ⟨117914,17,(.group 5 1560 false)⟩))
(.branch 117948
(.leaf ⟨117931,17,(.group 5 1561 false)⟩)
(.leaf ⟨117948,17,(.group 5 1562 false)⟩)))))))

theorem tree119_checked : tree119.check 116877 117965 = true := by decide +kernel

def tree120 : Tree := (.branch 118509
(.branch 118237
(.branch 118101
(.branch 118033
(.branch 117999
(.branch 117982
(.leaf ⟨117965,17,(.group 5 1563 false)⟩)
(.leaf ⟨117982,17,(.group 5 1564 false)⟩))
(.branch 118016
(.leaf ⟨117999,17,(.group 5 1565 false)⟩)
(.leaf ⟨118016,17,(.group 5 1566 false)⟩)))
(.branch 118067
(.branch 118050
(.leaf ⟨118033,17,(.group 5 1567 false)⟩)
(.leaf ⟨118050,17,(.group 5 1568 false)⟩))
(.branch 118084
(.leaf ⟨118067,17,(.group 5 1569 false)⟩)
(.leaf ⟨118084,17,(.group 5 1570 false)⟩))))
(.branch 118169
(.branch 118135
(.branch 118118
(.leaf ⟨118101,17,(.group 5 1571 false)⟩)
(.leaf ⟨118118,17,(.group 5 1572 false)⟩))
(.branch 118152
(.leaf ⟨118135,17,(.group 5 1573 false)⟩)
(.leaf ⟨118152,17,(.group 5 1574 false)⟩)))
(.branch 118203
(.branch 118186
(.leaf ⟨118169,17,(.group 5 1575 false)⟩)
(.leaf ⟨118186,17,(.group 5 1576 false)⟩))
(.branch 118220
(.leaf ⟨118203,17,(.group 5 1577 false)⟩)
(.leaf ⟨118220,17,(.group 5 1578 false)⟩)))))
(.branch 118373
(.branch 118305
(.branch 118271
(.branch 118254
(.leaf ⟨118237,17,(.group 5 1579 false)⟩)
(.leaf ⟨118254,17,(.group 5 1580 false)⟩))
(.branch 118288
(.leaf ⟨118271,17,(.group 5 1581 false)⟩)
(.leaf ⟨118288,17,(.group 5 1582 false)⟩)))
(.branch 118339
(.branch 118322
(.leaf ⟨118305,17,(.group 5 1583 false)⟩)
(.leaf ⟨118322,17,(.group 5 1584 false)⟩))
(.branch 118356
(.leaf ⟨118339,17,(.group 5 1585 false)⟩)
(.leaf ⟨118356,17,(.group 5 1586 false)⟩))))
(.branch 118441
(.branch 118407
(.branch 118390
(.leaf ⟨118373,17,(.group 5 1587 false)⟩)
(.leaf ⟨118390,17,(.group 5 1588 false)⟩))
(.branch 118424
(.leaf ⟨118407,17,(.group 5 1589 false)⟩)
(.leaf ⟨118424,17,(.group 5 1590 false)⟩)))
(.branch 118475
(.branch 118458
(.leaf ⟨118441,17,(.group 5 1591 false)⟩)
(.leaf ⟨118458,17,(.group 5 1592 false)⟩))
(.branch 118492
(.leaf ⟨118475,17,(.group 5 1593 false)⟩)
(.leaf ⟨118492,17,(.group 5 1594 false)⟩))))))
(.branch 118781
(.branch 118645
(.branch 118577
(.branch 118543
(.branch 118526
(.leaf ⟨118509,17,(.group 5 1595 false)⟩)
(.leaf ⟨118526,17,(.group 5 1596 false)⟩))
(.branch 118560
(.leaf ⟨118543,17,(.group 5 1597 false)⟩)
(.leaf ⟨118560,17,(.group 5 1598 false)⟩)))
(.branch 118611
(.branch 118594
(.leaf ⟨118577,17,(.group 5 1599 false)⟩)
(.leaf ⟨118594,17,(.group 5 1600 false)⟩))
(.branch 118628
(.leaf ⟨118611,17,(.group 5 1601 false)⟩)
(.leaf ⟨118628,17,(.group 5 1602 false)⟩))))
(.branch 118713
(.branch 118679
(.branch 118662
(.leaf ⟨118645,17,(.group 5 1603 false)⟩)
(.leaf ⟨118662,17,(.group 5 1604 false)⟩))
(.branch 118696
(.leaf ⟨118679,17,(.group 5 1605 false)⟩)
(.leaf ⟨118696,17,(.group 5 1606 false)⟩)))
(.branch 118747
(.branch 118730
(.leaf ⟨118713,17,(.group 5 1607 false)⟩)
(.leaf ⟨118730,17,(.group 5 1608 false)⟩))
(.branch 118764
(.leaf ⟨118747,17,(.group 5 1609 false)⟩)
(.leaf ⟨118764,17,(.group 5 1610 false)⟩)))))
(.branch 118917
(.branch 118849
(.branch 118815
(.branch 118798
(.leaf ⟨118781,17,(.group 5 1611 false)⟩)
(.leaf ⟨118798,17,(.group 5 1612 false)⟩))
(.branch 118832
(.leaf ⟨118815,17,(.group 5 1613 false)⟩)
(.leaf ⟨118832,17,(.group 5 1614 false)⟩)))
(.branch 118883
(.branch 118866
(.leaf ⟨118849,17,(.group 5 1615 false)⟩)
(.leaf ⟨118866,17,(.group 5 1616 false)⟩))
(.branch 118900
(.leaf ⟨118883,17,(.group 5 1617 false)⟩)
(.leaf ⟨118900,17,(.group 5 1618 false)⟩))))
(.branch 118985
(.branch 118951
(.branch 118934
(.leaf ⟨118917,17,(.group 5 1619 false)⟩)
(.leaf ⟨118934,17,(.group 5 1620 false)⟩))
(.branch 118968
(.leaf ⟨118951,17,(.group 5 1621 false)⟩)
(.leaf ⟨118968,17,(.group 5 1622 false)⟩)))
(.branch 119019
(.branch 119002
(.leaf ⟨118985,17,(.group 5 1623 false)⟩)
(.leaf ⟨119002,17,(.group 5 1624 false)⟩))
(.branch 119036
(.leaf ⟨119019,17,(.group 5 1625 false)⟩)
(.leaf ⟨119036,17,(.group 5 1626 false)⟩)))))))

theorem tree120_checked : tree120.check 117965 119053 = true := by decide +kernel

def tree121 : Tree := (.branch 119597
(.branch 119325
(.branch 119189
(.branch 119121
(.branch 119087
(.branch 119070
(.leaf ⟨119053,17,(.group 5 1627 false)⟩)
(.leaf ⟨119070,17,(.group 5 1628 false)⟩))
(.branch 119104
(.leaf ⟨119087,17,(.group 5 1629 false)⟩)
(.leaf ⟨119104,17,(.group 5 1630 false)⟩)))
(.branch 119155
(.branch 119138
(.leaf ⟨119121,17,(.group 5 1631 false)⟩)
(.leaf ⟨119138,17,(.group 5 1632 false)⟩))
(.branch 119172
(.leaf ⟨119155,17,(.group 5 1633 false)⟩)
(.leaf ⟨119172,17,(.group 5 1634 false)⟩))))
(.branch 119257
(.branch 119223
(.branch 119206
(.leaf ⟨119189,17,(.group 5 1635 false)⟩)
(.leaf ⟨119206,17,(.group 5 1636 false)⟩))
(.branch 119240
(.leaf ⟨119223,17,(.group 5 1637 false)⟩)
(.leaf ⟨119240,17,(.group 5 1638 false)⟩)))
(.branch 119291
(.branch 119274
(.leaf ⟨119257,17,(.group 5 1639 false)⟩)
(.leaf ⟨119274,17,(.group 5 1640 false)⟩))
(.branch 119308
(.leaf ⟨119291,17,(.group 5 1641 false)⟩)
(.leaf ⟨119308,17,(.group 5 1642 false)⟩)))))
(.branch 119461
(.branch 119393
(.branch 119359
(.branch 119342
(.leaf ⟨119325,17,(.group 5 1643 false)⟩)
(.leaf ⟨119342,17,(.group 5 1644 false)⟩))
(.branch 119376
(.leaf ⟨119359,17,(.group 5 1645 false)⟩)
(.leaf ⟨119376,17,(.group 5 1646 false)⟩)))
(.branch 119427
(.branch 119410
(.leaf ⟨119393,17,(.group 5 1647 false)⟩)
(.leaf ⟨119410,17,(.group 5 1648 false)⟩))
(.branch 119444
(.leaf ⟨119427,17,(.group 5 1649 false)⟩)
(.leaf ⟨119444,17,(.group 5 1650 false)⟩))))
(.branch 119529
(.branch 119495
(.branch 119478
(.leaf ⟨119461,17,(.group 5 1651 false)⟩)
(.leaf ⟨119478,17,(.group 5 1652 false)⟩))
(.branch 119512
(.leaf ⟨119495,17,(.group 5 1653 false)⟩)
(.leaf ⟨119512,17,(.group 5 1654 false)⟩)))
(.branch 119563
(.branch 119546
(.leaf ⟨119529,17,(.group 5 1655 false)⟩)
(.leaf ⟨119546,17,(.group 5 1656 false)⟩))
(.branch 119580
(.leaf ⟨119563,17,(.group 5 1657 false)⟩)
(.leaf ⟨119580,17,(.group 5 1658 false)⟩))))))
(.branch 119869
(.branch 119733
(.branch 119665
(.branch 119631
(.branch 119614
(.leaf ⟨119597,17,(.group 5 1659 false)⟩)
(.leaf ⟨119614,17,(.group 5 1660 false)⟩))
(.branch 119648
(.leaf ⟨119631,17,(.group 5 1661 false)⟩)
(.leaf ⟨119648,17,(.group 5 1662 false)⟩)))
(.branch 119699
(.branch 119682
(.leaf ⟨119665,17,(.group 5 1663 false)⟩)
(.leaf ⟨119682,17,(.group 5 1664 false)⟩))
(.branch 119716
(.leaf ⟨119699,17,(.group 5 1665 false)⟩)
(.leaf ⟨119716,17,(.group 5 1666 false)⟩))))
(.branch 119801
(.branch 119767
(.branch 119750
(.leaf ⟨119733,17,(.group 5 1667 false)⟩)
(.leaf ⟨119750,17,(.group 5 1668 false)⟩))
(.branch 119784
(.leaf ⟨119767,17,(.group 5 1669 false)⟩)
(.leaf ⟨119784,17,(.group 5 1670 false)⟩)))
(.branch 119835
(.branch 119818
(.leaf ⟨119801,17,(.group 5 1671 false)⟩)
(.leaf ⟨119818,17,(.group 5 1672 false)⟩))
(.branch 119852
(.leaf ⟨119835,17,(.group 5 1673 false)⟩)
(.leaf ⟨119852,17,(.group 5 1674 false)⟩)))))
(.branch 120005
(.branch 119937
(.branch 119903
(.branch 119886
(.leaf ⟨119869,17,(.group 5 1675 false)⟩)
(.leaf ⟨119886,17,(.group 5 1676 false)⟩))
(.branch 119920
(.leaf ⟨119903,17,(.group 5 1677 false)⟩)
(.leaf ⟨119920,17,(.group 5 1678 false)⟩)))
(.branch 119971
(.branch 119954
(.leaf ⟨119937,17,(.group 5 1679 false)⟩)
(.leaf ⟨119954,17,(.group 5 1680 false)⟩))
(.branch 119988
(.leaf ⟨119971,17,(.group 5 1681 false)⟩)
(.leaf ⟨119988,17,(.group 5 1682 false)⟩))))
(.branch 120073
(.branch 120039
(.branch 120022
(.leaf ⟨120005,17,(.group 5 1683 false)⟩)
(.leaf ⟨120022,17,(.group 5 1684 false)⟩))
(.branch 120056
(.leaf ⟨120039,17,(.group 5 1685 false)⟩)
(.leaf ⟨120056,17,(.group 5 1686 false)⟩)))
(.branch 120107
(.branch 120090
(.leaf ⟨120073,17,(.group 5 1687 false)⟩)
(.leaf ⟨120090,17,(.group 5 1688 false)⟩))
(.branch 120124
(.leaf ⟨120107,17,(.group 5 1689 false)⟩)
(.leaf ⟨120124,17,(.group 5 1690 false)⟩)))))))

theorem tree121_checked : tree121.check 119053 120141 = true := by decide +kernel

def tree122 : Tree := (.branch 120685
(.branch 120413
(.branch 120277
(.branch 120209
(.branch 120175
(.branch 120158
(.leaf ⟨120141,17,(.group 5 1691 false)⟩)
(.leaf ⟨120158,17,(.group 5 1692 false)⟩))
(.branch 120192
(.leaf ⟨120175,17,(.group 5 1693 false)⟩)
(.leaf ⟨120192,17,(.group 5 1694 false)⟩)))
(.branch 120243
(.branch 120226
(.leaf ⟨120209,17,(.group 5 1695 false)⟩)
(.leaf ⟨120226,17,(.group 5 1696 false)⟩))
(.branch 120260
(.leaf ⟨120243,17,(.group 5 1697 false)⟩)
(.leaf ⟨120260,17,(.group 5 1698 false)⟩))))
(.branch 120345
(.branch 120311
(.branch 120294
(.leaf ⟨120277,17,(.group 5 1699 false)⟩)
(.leaf ⟨120294,17,(.group 5 1700 false)⟩))
(.branch 120328
(.leaf ⟨120311,17,(.group 5 1701 false)⟩)
(.leaf ⟨120328,17,(.group 5 1702 false)⟩)))
(.branch 120379
(.branch 120362
(.leaf ⟨120345,17,(.group 5 1703 false)⟩)
(.leaf ⟨120362,17,(.group 5 1704 false)⟩))
(.branch 120396
(.leaf ⟨120379,17,(.group 5 1705 false)⟩)
(.leaf ⟨120396,17,(.group 5 1706 false)⟩)))))
(.branch 120549
(.branch 120481
(.branch 120447
(.branch 120430
(.leaf ⟨120413,17,(.group 5 1707 false)⟩)
(.leaf ⟨120430,17,(.group 5 1708 false)⟩))
(.branch 120464
(.leaf ⟨120447,17,(.group 5 1709 false)⟩)
(.leaf ⟨120464,17,(.group 5 1710 false)⟩)))
(.branch 120515
(.branch 120498
(.leaf ⟨120481,17,(.group 5 1711 false)⟩)
(.leaf ⟨120498,17,(.group 5 1712 false)⟩))
(.branch 120532
(.leaf ⟨120515,17,(.group 5 1713 false)⟩)
(.leaf ⟨120532,17,(.group 5 1714 false)⟩))))
(.branch 120617
(.branch 120583
(.branch 120566
(.leaf ⟨120549,17,(.group 5 1715 false)⟩)
(.leaf ⟨120566,17,(.group 5 1716 false)⟩))
(.branch 120600
(.leaf ⟨120583,17,(.group 5 1717 false)⟩)
(.leaf ⟨120600,17,(.group 5 1718 false)⟩)))
(.branch 120651
(.branch 120634
(.leaf ⟨120617,17,(.group 5 1719 false)⟩)
(.leaf ⟨120634,17,(.group 5 1720 false)⟩))
(.branch 120668
(.leaf ⟨120651,17,(.group 5 1721 false)⟩)
(.leaf ⟨120668,17,(.group 5 1722 false)⟩))))))
(.branch 120957
(.branch 120821
(.branch 120753
(.branch 120719
(.branch 120702
(.leaf ⟨120685,17,(.group 5 1723 false)⟩)
(.leaf ⟨120702,17,(.group 5 1724 false)⟩))
(.branch 120736
(.leaf ⟨120719,17,(.group 5 1725 false)⟩)
(.leaf ⟨120736,17,(.group 5 1726 false)⟩)))
(.branch 120787
(.branch 120770
(.leaf ⟨120753,17,(.group 5 1727 false)⟩)
(.leaf ⟨120770,17,(.group 5 1728 false)⟩))
(.branch 120804
(.leaf ⟨120787,17,(.group 5 1729 false)⟩)
(.leaf ⟨120804,17,(.group 5 1730 false)⟩))))
(.branch 120889
(.branch 120855
(.branch 120838
(.leaf ⟨120821,17,(.group 5 1731 false)⟩)
(.leaf ⟨120838,17,(.group 5 1732 false)⟩))
(.branch 120872
(.leaf ⟨120855,17,(.group 5 1733 false)⟩)
(.leaf ⟨120872,17,(.group 5 1734 false)⟩)))
(.branch 120923
(.branch 120906
(.leaf ⟨120889,17,(.group 5 1735 false)⟩)
(.leaf ⟨120906,17,(.group 5 1736 false)⟩))
(.branch 120940
(.leaf ⟨120923,17,(.group 5 1737 false)⟩)
(.leaf ⟨120940,17,(.group 5 1738 false)⟩)))))
(.branch 121093
(.branch 121025
(.branch 120991
(.branch 120974
(.leaf ⟨120957,17,(.group 5 1739 false)⟩)
(.leaf ⟨120974,17,(.group 5 1740 false)⟩))
(.branch 121008
(.leaf ⟨120991,17,(.group 5 1741 false)⟩)
(.leaf ⟨121008,17,(.group 5 1742 false)⟩)))
(.branch 121059
(.branch 121042
(.leaf ⟨121025,17,(.group 5 1743 false)⟩)
(.leaf ⟨121042,17,(.group 5 1744 false)⟩))
(.branch 121076
(.leaf ⟨121059,17,(.group 5 1745 false)⟩)
(.leaf ⟨121076,17,(.group 5 1746 false)⟩))))
(.branch 121161
(.branch 121127
(.branch 121110
(.leaf ⟨121093,17,(.group 5 1747 false)⟩)
(.leaf ⟨121110,17,(.group 5 1748 false)⟩))
(.branch 121144
(.leaf ⟨121127,17,(.group 5 1749 false)⟩)
(.leaf ⟨121144,17,(.group 5 1750 false)⟩)))
(.branch 121195
(.branch 121178
(.leaf ⟨121161,17,(.group 5 1751 false)⟩)
(.leaf ⟨121178,17,(.group 5 1752 false)⟩))
(.branch 121212
(.leaf ⟨121195,17,(.group 5 1753 false)⟩)
(.leaf ⟨121212,17,(.group 5 1754 false)⟩)))))))

theorem tree122_checked : tree122.check 120141 121229 = true := by decide +kernel

def tree123 : Tree := (.branch 121773
(.branch 121501
(.branch 121365
(.branch 121297
(.branch 121263
(.branch 121246
(.leaf ⟨121229,17,(.group 5 1755 false)⟩)
(.leaf ⟨121246,17,(.group 5 1756 false)⟩))
(.branch 121280
(.leaf ⟨121263,17,(.group 5 1757 false)⟩)
(.leaf ⟨121280,17,(.group 5 1758 false)⟩)))
(.branch 121331
(.branch 121314
(.leaf ⟨121297,17,(.group 5 1759 false)⟩)
(.leaf ⟨121314,17,(.group 5 1760 false)⟩))
(.branch 121348
(.leaf ⟨121331,17,(.group 5 1761 false)⟩)
(.leaf ⟨121348,17,(.group 5 1762 false)⟩))))
(.branch 121433
(.branch 121399
(.branch 121382
(.leaf ⟨121365,17,(.group 5 1763 false)⟩)
(.leaf ⟨121382,17,(.group 5 1764 false)⟩))
(.branch 121416
(.leaf ⟨121399,17,(.group 5 1765 false)⟩)
(.leaf ⟨121416,17,(.group 5 1766 false)⟩)))
(.branch 121467
(.branch 121450
(.leaf ⟨121433,17,(.group 5 1767 false)⟩)
(.leaf ⟨121450,17,(.group 5 1768 false)⟩))
(.branch 121484
(.leaf ⟨121467,17,(.group 5 1769 false)⟩)
(.leaf ⟨121484,17,(.group 5 1770 false)⟩)))))
(.branch 121637
(.branch 121569
(.branch 121535
(.branch 121518
(.leaf ⟨121501,17,(.group 5 1771 false)⟩)
(.leaf ⟨121518,17,(.group 5 1772 false)⟩))
(.branch 121552
(.leaf ⟨121535,17,(.group 5 1773 false)⟩)
(.leaf ⟨121552,17,(.group 5 1774 false)⟩)))
(.branch 121603
(.branch 121586
(.leaf ⟨121569,17,(.group 5 1775 false)⟩)
(.leaf ⟨121586,17,(.group 5 1776 false)⟩))
(.branch 121620
(.leaf ⟨121603,17,(.group 5 1777 false)⟩)
(.leaf ⟨121620,17,(.group 5 1778 false)⟩))))
(.branch 121705
(.branch 121671
(.branch 121654
(.leaf ⟨121637,17,(.group 5 1779 false)⟩)
(.leaf ⟨121654,17,(.group 5 1780 false)⟩))
(.branch 121688
(.leaf ⟨121671,17,(.group 5 1781 false)⟩)
(.leaf ⟨121688,17,(.group 5 1782 false)⟩)))
(.branch 121739
(.branch 121722
(.leaf ⟨121705,17,(.group 5 1783 false)⟩)
(.leaf ⟨121722,17,(.group 5 1784 false)⟩))
(.branch 121756
(.leaf ⟨121739,17,(.group 5 1785 false)⟩)
(.leaf ⟨121756,17,(.group 5 1786 false)⟩))))))
(.branch 122045
(.branch 121909
(.branch 121841
(.branch 121807
(.branch 121790
(.leaf ⟨121773,17,(.group 5 1787 false)⟩)
(.leaf ⟨121790,17,(.group 5 1788 false)⟩))
(.branch 121824
(.leaf ⟨121807,17,(.group 5 1789 false)⟩)
(.leaf ⟨121824,17,(.group 5 1790 false)⟩)))
(.branch 121875
(.branch 121858
(.leaf ⟨121841,17,(.group 5 1791 false)⟩)
(.leaf ⟨121858,17,(.group 5 1792 false)⟩))
(.branch 121892
(.leaf ⟨121875,17,(.group 5 1793 false)⟩)
(.leaf ⟨121892,17,(.group 5 1794 false)⟩))))
(.branch 121977
(.branch 121943
(.branch 121926
(.leaf ⟨121909,17,(.group 5 1795 false)⟩)
(.leaf ⟨121926,17,(.group 5 1796 false)⟩))
(.branch 121960
(.leaf ⟨121943,17,(.group 5 1797 false)⟩)
(.leaf ⟨121960,17,(.group 5 1798 false)⟩)))
(.branch 122011
(.branch 121994
(.leaf ⟨121977,17,(.group 5 1799 false)⟩)
(.leaf ⟨121994,17,(.group 5 1800 false)⟩))
(.branch 122028
(.leaf ⟨122011,17,(.group 5 1801 false)⟩)
(.leaf ⟨122028,17,(.group 5 1802 false)⟩)))))
(.branch 122181
(.branch 122113
(.branch 122079
(.branch 122062
(.leaf ⟨122045,17,(.group 5 1803 false)⟩)
(.leaf ⟨122062,17,(.group 5 1804 false)⟩))
(.branch 122096
(.leaf ⟨122079,17,(.group 5 1805 false)⟩)
(.leaf ⟨122096,17,(.group 5 1806 false)⟩)))
(.branch 122147
(.branch 122130
(.leaf ⟨122113,17,(.group 5 1807 false)⟩)
(.leaf ⟨122130,17,(.group 5 1808 false)⟩))
(.branch 122164
(.leaf ⟨122147,17,(.group 5 1809 false)⟩)
(.leaf ⟨122164,17,(.group 5 1810 false)⟩))))
(.branch 122249
(.branch 122215
(.branch 122198
(.leaf ⟨122181,17,(.group 5 1811 false)⟩)
(.leaf ⟨122198,17,(.group 5 1812 false)⟩))
(.branch 122232
(.leaf ⟨122215,17,(.group 5 1813 false)⟩)
(.leaf ⟨122232,17,(.group 5 1814 false)⟩)))
(.branch 122283
(.branch 122266
(.leaf ⟨122249,17,(.group 5 1815 false)⟩)
(.leaf ⟨122266,17,(.group 5 1816 false)⟩))
(.branch 122300
(.leaf ⟨122283,17,(.group 5 1817 false)⟩)
(.leaf ⟨122300,17,(.group 5 1818 false)⟩)))))))

theorem tree123_checked : tree123.check 121229 122317 = true := by decide +kernel

def tree124 : Tree := (.branch 122861
(.branch 122589
(.branch 122453
(.branch 122385
(.branch 122351
(.branch 122334
(.leaf ⟨122317,17,(.group 5 1819 false)⟩)
(.leaf ⟨122334,17,(.group 5 1820 false)⟩))
(.branch 122368
(.leaf ⟨122351,17,(.group 5 1821 false)⟩)
(.leaf ⟨122368,17,(.group 5 1822 false)⟩)))
(.branch 122419
(.branch 122402
(.leaf ⟨122385,17,(.group 5 1823 false)⟩)
(.leaf ⟨122402,17,(.group 5 1824 false)⟩))
(.branch 122436
(.leaf ⟨122419,17,(.group 5 1825 false)⟩)
(.leaf ⟨122436,17,(.group 5 1826 false)⟩))))
(.branch 122521
(.branch 122487
(.branch 122470
(.leaf ⟨122453,17,(.group 5 1827 false)⟩)
(.leaf ⟨122470,17,(.group 5 1828 false)⟩))
(.branch 122504
(.leaf ⟨122487,17,(.group 5 1829 false)⟩)
(.leaf ⟨122504,17,(.group 5 1830 false)⟩)))
(.branch 122555
(.branch 122538
(.leaf ⟨122521,17,(.group 5 1831 false)⟩)
(.leaf ⟨122538,17,(.group 5 1832 false)⟩))
(.branch 122572
(.leaf ⟨122555,17,(.group 5 1833 false)⟩)
(.leaf ⟨122572,17,(.group 5 1834 false)⟩)))))
(.branch 122725
(.branch 122657
(.branch 122623
(.branch 122606
(.leaf ⟨122589,17,(.group 5 1835 false)⟩)
(.leaf ⟨122606,17,(.group 5 1836 false)⟩))
(.branch 122640
(.leaf ⟨122623,17,(.group 5 1837 false)⟩)
(.leaf ⟨122640,17,(.group 5 1838 false)⟩)))
(.branch 122691
(.branch 122674
(.leaf ⟨122657,17,(.group 5 1839 false)⟩)
(.leaf ⟨122674,17,(.group 5 1840 false)⟩))
(.branch 122708
(.leaf ⟨122691,17,(.group 5 1841 false)⟩)
(.leaf ⟨122708,17,(.group 5 1842 false)⟩))))
(.branch 122793
(.branch 122759
(.branch 122742
(.leaf ⟨122725,17,(.group 5 1843 false)⟩)
(.leaf ⟨122742,17,(.group 5 1844 false)⟩))
(.branch 122776
(.leaf ⟨122759,17,(.group 5 1845 false)⟩)
(.leaf ⟨122776,17,(.group 5 1846 false)⟩)))
(.branch 122827
(.branch 122810
(.leaf ⟨122793,17,(.group 5 1847 false)⟩)
(.leaf ⟨122810,17,(.group 5 1848 false)⟩))
(.branch 122844
(.leaf ⟨122827,17,(.group 5 1849 false)⟩)
(.leaf ⟨122844,17,(.group 5 1850 false)⟩))))))
(.branch 123133
(.branch 122997
(.branch 122929
(.branch 122895
(.branch 122878
(.leaf ⟨122861,17,(.group 5 1851 false)⟩)
(.leaf ⟨122878,17,(.group 5 1852 false)⟩))
(.branch 122912
(.leaf ⟨122895,17,(.group 5 1853 false)⟩)
(.leaf ⟨122912,17,(.group 5 1854 false)⟩)))
(.branch 122963
(.branch 122946
(.leaf ⟨122929,17,(.group 5 1855 false)⟩)
(.leaf ⟨122946,17,(.group 5 1856 false)⟩))
(.branch 122980
(.leaf ⟨122963,17,(.group 5 1857 false)⟩)
(.leaf ⟨122980,17,(.group 5 1858 false)⟩))))
(.branch 123065
(.branch 123031
(.branch 123014
(.leaf ⟨122997,17,(.group 5 1859 false)⟩)
(.leaf ⟨123014,17,(.group 5 1860 false)⟩))
(.branch 123048
(.leaf ⟨123031,17,(.group 5 1861 false)⟩)
(.leaf ⟨123048,17,(.group 5 1862 false)⟩)))
(.branch 123099
(.branch 123082
(.leaf ⟨123065,17,(.group 5 1863 false)⟩)
(.leaf ⟨123082,17,(.group 5 1864 false)⟩))
(.branch 123116
(.leaf ⟨123099,17,(.group 5 1865 false)⟩)
(.leaf ⟨123116,17,(.group 5 1866 false)⟩)))))
(.branch 123269
(.branch 123201
(.branch 123167
(.branch 123150
(.leaf ⟨123133,17,(.group 5 1867 false)⟩)
(.leaf ⟨123150,17,(.group 5 1868 false)⟩))
(.branch 123184
(.leaf ⟨123167,17,(.group 5 1869 false)⟩)
(.leaf ⟨123184,17,(.group 5 1870 false)⟩)))
(.branch 123235
(.branch 123218
(.leaf ⟨123201,17,(.group 5 1871 false)⟩)
(.leaf ⟨123218,17,(.group 5 1872 false)⟩))
(.branch 123252
(.leaf ⟨123235,17,(.group 5 1873 false)⟩)
(.leaf ⟨123252,17,(.group 5 1874 false)⟩))))
(.branch 123337
(.branch 123303
(.branch 123286
(.leaf ⟨123269,17,(.group 5 1875 false)⟩)
(.leaf ⟨123286,17,(.group 5 1876 false)⟩))
(.branch 123320
(.leaf ⟨123303,17,(.group 6 950 false)⟩)
(.leaf ⟨123320,17,(.group 6 951 false)⟩)))
(.branch 123371
(.branch 123354
(.leaf ⟨123337,17,(.group 6 952 false)⟩)
(.leaf ⟨123354,17,(.group 6 953 false)⟩))
(.branch 123388
(.leaf ⟨123371,17,(.group 6 954 false)⟩)
(.leaf ⟨123388,17,(.group 6 955 false)⟩)))))))

theorem tree124_checked : tree124.check 122317 123405 = true := by decide +kernel

def tree125 : Tree := (.branch 123949
(.branch 123677
(.branch 123541
(.branch 123473
(.branch 123439
(.branch 123422
(.leaf ⟨123405,17,(.group 6 956 false)⟩)
(.leaf ⟨123422,17,(.group 6 957 false)⟩))
(.branch 123456
(.leaf ⟨123439,17,(.group 6 958 false)⟩)
(.leaf ⟨123456,17,(.group 6 959 false)⟩)))
(.branch 123507
(.branch 123490
(.leaf ⟨123473,17,(.group 6 960 false)⟩)
(.leaf ⟨123490,17,(.group 6 961 false)⟩))
(.branch 123524
(.leaf ⟨123507,17,(.group 6 962 false)⟩)
(.leaf ⟨123524,17,(.group 6 963 false)⟩))))
(.branch 123609
(.branch 123575
(.branch 123558
(.leaf ⟨123541,17,(.group 6 964 false)⟩)
(.leaf ⟨123558,17,(.group 6 965 false)⟩))
(.branch 123592
(.leaf ⟨123575,17,(.group 6 966 false)⟩)
(.leaf ⟨123592,17,(.group 6 967 false)⟩)))
(.branch 123643
(.branch 123626
(.leaf ⟨123609,17,(.group 6 968 false)⟩)
(.leaf ⟨123626,17,(.group 6 969 false)⟩))
(.branch 123660
(.leaf ⟨123643,17,(.group 6 970 false)⟩)
(.leaf ⟨123660,17,(.group 6 971 false)⟩)))))
(.branch 123813
(.branch 123745
(.branch 123711
(.branch 123694
(.leaf ⟨123677,17,(.group 6 972 false)⟩)
(.leaf ⟨123694,17,(.group 6 973 false)⟩))
(.branch 123728
(.leaf ⟨123711,17,(.group 6 974 false)⟩)
(.leaf ⟨123728,17,(.group 6 975 false)⟩)))
(.branch 123779
(.branch 123762
(.leaf ⟨123745,17,(.group 6 976 false)⟩)
(.leaf ⟨123762,17,(.group 6 977 false)⟩))
(.branch 123796
(.leaf ⟨123779,17,(.group 6 978 false)⟩)
(.leaf ⟨123796,17,(.group 6 979 false)⟩))))
(.branch 123881
(.branch 123847
(.branch 123830
(.leaf ⟨123813,17,(.group 6 980 false)⟩)
(.leaf ⟨123830,17,(.group 6 981 false)⟩))
(.branch 123864
(.leaf ⟨123847,17,(.group 6 982 false)⟩)
(.leaf ⟨123864,17,(.group 6 983 false)⟩)))
(.branch 123915
(.branch 123898
(.leaf ⟨123881,17,(.group 6 984 false)⟩)
(.leaf ⟨123898,17,(.group 6 985 false)⟩))
(.branch 123932
(.leaf ⟨123915,17,(.group 6 986 false)⟩)
(.leaf ⟨123932,17,(.group 6 987 false)⟩))))))
(.branch 124221
(.branch 124085
(.branch 124017
(.branch 123983
(.branch 123966
(.leaf ⟨123949,17,(.group 6 988 false)⟩)
(.leaf ⟨123966,17,(.group 6 989 false)⟩))
(.branch 124000
(.leaf ⟨123983,17,(.group 6 990 false)⟩)
(.leaf ⟨124000,17,(.group 6 991 false)⟩)))
(.branch 124051
(.branch 124034
(.leaf ⟨124017,17,(.group 6 992 false)⟩)
(.leaf ⟨124034,17,(.group 6 993 false)⟩))
(.branch 124068
(.leaf ⟨124051,17,(.group 6 994 false)⟩)
(.leaf ⟨124068,17,(.group 6 995 false)⟩))))
(.branch 124153
(.branch 124119
(.branch 124102
(.leaf ⟨124085,17,(.group 6 996 false)⟩)
(.leaf ⟨124102,17,(.group 6 997 false)⟩))
(.branch 124136
(.leaf ⟨124119,17,(.group 6 998 false)⟩)
(.leaf ⟨124136,17,(.group 6 999 false)⟩)))
(.branch 124187
(.branch 124170
(.leaf ⟨124153,17,(.group 6 1000 false)⟩)
(.leaf ⟨124170,17,(.group 6 1001 false)⟩))
(.branch 124204
(.leaf ⟨124187,17,(.group 6 1002 false)⟩)
(.leaf ⟨124204,17,(.group 6 1003 false)⟩)))))
(.branch 124357
(.branch 124289
(.branch 124255
(.branch 124238
(.leaf ⟨124221,17,(.group 6 1004 false)⟩)
(.leaf ⟨124238,17,(.group 6 1005 false)⟩))
(.branch 124272
(.leaf ⟨124255,17,(.group 6 1006 false)⟩)
(.leaf ⟨124272,17,(.group 6 1007 false)⟩)))
(.branch 124323
(.branch 124306
(.leaf ⟨124289,17,(.group 6 1008 false)⟩)
(.leaf ⟨124306,17,(.group 6 1009 false)⟩))
(.branch 124340
(.leaf ⟨124323,17,(.group 6 1010 false)⟩)
(.leaf ⟨124340,17,(.group 6 1011 false)⟩))))
(.branch 124425
(.branch 124391
(.branch 124374
(.leaf ⟨124357,17,(.group 6 1012 false)⟩)
(.leaf ⟨124374,17,(.group 6 1013 false)⟩))
(.branch 124408
(.leaf ⟨124391,17,(.group 6 1014 false)⟩)
(.leaf ⟨124408,17,(.group 6 1015 false)⟩)))
(.branch 124459
(.branch 124442
(.leaf ⟨124425,17,(.group 6 1016 false)⟩)
(.leaf ⟨124442,17,(.group 6 1017 false)⟩))
(.branch 124476
(.leaf ⟨124459,17,(.group 6 1018 false)⟩)
(.leaf ⟨124476,17,(.group 6 1019 false)⟩)))))))

theorem tree125_checked : tree125.check 123405 124493 = true := by decide +kernel

def tree126 : Tree := (.branch 125037
(.branch 124765
(.branch 124629
(.branch 124561
(.branch 124527
(.branch 124510
(.leaf ⟨124493,17,(.group 6 1020 false)⟩)
(.leaf ⟨124510,17,(.group 6 1021 false)⟩))
(.branch 124544
(.leaf ⟨124527,17,(.group 6 1022 false)⟩)
(.leaf ⟨124544,17,(.group 6 1023 false)⟩)))
(.branch 124595
(.branch 124578
(.leaf ⟨124561,17,(.group 6 1024 false)⟩)
(.leaf ⟨124578,17,(.group 6 1025 false)⟩))
(.branch 124612
(.leaf ⟨124595,17,(.group 6 1026 false)⟩)
(.leaf ⟨124612,17,(.group 6 1027 false)⟩))))
(.branch 124697
(.branch 124663
(.branch 124646
(.leaf ⟨124629,17,(.group 6 1028 false)⟩)
(.leaf ⟨124646,17,(.group 6 1029 false)⟩))
(.branch 124680
(.leaf ⟨124663,17,(.group 6 1030 false)⟩)
(.leaf ⟨124680,17,(.group 6 1031 false)⟩)))
(.branch 124731
(.branch 124714
(.leaf ⟨124697,17,(.group 6 1032 false)⟩)
(.leaf ⟨124714,17,(.group 6 1033 false)⟩))
(.branch 124748
(.leaf ⟨124731,17,(.group 6 1034 false)⟩)
(.leaf ⟨124748,17,(.group 6 1035 false)⟩)))))
(.branch 124901
(.branch 124833
(.branch 124799
(.branch 124782
(.leaf ⟨124765,17,(.group 6 1036 false)⟩)
(.leaf ⟨124782,17,(.group 6 1037 false)⟩))
(.branch 124816
(.leaf ⟨124799,17,(.group 6 1038 false)⟩)
(.leaf ⟨124816,17,(.group 6 1039 false)⟩)))
(.branch 124867
(.branch 124850
(.leaf ⟨124833,17,(.group 6 1040 false)⟩)
(.leaf ⟨124850,17,(.group 6 1041 false)⟩))
(.branch 124884
(.leaf ⟨124867,17,(.group 6 1042 false)⟩)
(.leaf ⟨124884,17,(.group 6 1043 false)⟩))))
(.branch 124969
(.branch 124935
(.branch 124918
(.leaf ⟨124901,17,(.group 6 1044 false)⟩)
(.leaf ⟨124918,17,(.group 6 1045 false)⟩))
(.branch 124952
(.leaf ⟨124935,17,(.group 6 1046 false)⟩)
(.leaf ⟨124952,17,(.group 6 1047 false)⟩)))
(.branch 125003
(.branch 124986
(.leaf ⟨124969,17,(.group 6 1048 false)⟩)
(.leaf ⟨124986,17,(.group 6 1049 false)⟩))
(.branch 125020
(.leaf ⟨125003,17,(.group 6 1050 false)⟩)
(.leaf ⟨125020,17,(.group 6 1051 false)⟩))))))
(.branch 125309
(.branch 125173
(.branch 125105
(.branch 125071
(.branch 125054
(.leaf ⟨125037,17,(.group 6 1052 false)⟩)
(.leaf ⟨125054,17,(.group 6 1053 false)⟩))
(.branch 125088
(.leaf ⟨125071,17,(.group 6 1054 false)⟩)
(.leaf ⟨125088,17,(.group 6 1055 false)⟩)))
(.branch 125139
(.branch 125122
(.leaf ⟨125105,17,(.group 6 1056 false)⟩)
(.leaf ⟨125122,17,(.group 6 1057 false)⟩))
(.branch 125156
(.leaf ⟨125139,17,(.group 6 1058 false)⟩)
(.leaf ⟨125156,17,(.group 6 1059 false)⟩))))
(.branch 125241
(.branch 125207
(.branch 125190
(.leaf ⟨125173,17,(.group 6 1060 false)⟩)
(.leaf ⟨125190,17,(.group 6 1061 false)⟩))
(.branch 125224
(.leaf ⟨125207,17,(.group 6 1062 false)⟩)
(.leaf ⟨125224,17,(.group 6 1063 false)⟩)))
(.branch 125275
(.branch 125258
(.leaf ⟨125241,17,(.group 6 1064 false)⟩)
(.leaf ⟨125258,17,(.group 6 1065 false)⟩))
(.branch 125292
(.leaf ⟨125275,17,(.group 6 1066 false)⟩)
(.leaf ⟨125292,17,(.group 6 1067 false)⟩)))))
(.branch 125445
(.branch 125377
(.branch 125343
(.branch 125326
(.leaf ⟨125309,17,(.group 6 1068 false)⟩)
(.leaf ⟨125326,17,(.group 6 1069 false)⟩))
(.branch 125360
(.leaf ⟨125343,17,(.group 6 1070 false)⟩)
(.leaf ⟨125360,17,(.group 6 1071 false)⟩)))
(.branch 125411
(.branch 125394
(.leaf ⟨125377,17,(.group 6 1072 false)⟩)
(.leaf ⟨125394,17,(.group 6 1073 false)⟩))
(.branch 125428
(.leaf ⟨125411,17,(.group 6 1074 false)⟩)
(.leaf ⟨125428,17,(.group 6 1075 false)⟩))))
(.branch 125513
(.branch 125479
(.branch 125462
(.leaf ⟨125445,17,(.group 6 1076 false)⟩)
(.leaf ⟨125462,17,(.group 6 1077 false)⟩))
(.branch 125496
(.leaf ⟨125479,17,(.group 6 1078 false)⟩)
(.leaf ⟨125496,17,(.group 6 1079 false)⟩)))
(.branch 125547
(.branch 125530
(.leaf ⟨125513,17,(.group 6 1080 false)⟩)
(.leaf ⟨125530,17,(.group 6 1081 false)⟩))
(.branch 125564
(.leaf ⟨125547,17,(.group 6 1082 false)⟩)
(.leaf ⟨125564,17,(.group 6 1083 false)⟩)))))))

theorem tree126_checked : tree126.check 124493 125581 = true := by decide +kernel

def tree127 : Tree := (.branch 126125
(.branch 125853
(.branch 125717
(.branch 125649
(.branch 125615
(.branch 125598
(.leaf ⟨125581,17,(.group 6 1084 false)⟩)
(.leaf ⟨125598,17,(.group 6 1085 false)⟩))
(.branch 125632
(.leaf ⟨125615,17,(.group 6 1086 false)⟩)
(.leaf ⟨125632,17,(.group 6 1087 false)⟩)))
(.branch 125683
(.branch 125666
(.leaf ⟨125649,17,(.group 6 1088 false)⟩)
(.leaf ⟨125666,17,(.group 6 1089 false)⟩))
(.branch 125700
(.leaf ⟨125683,17,(.group 6 1090 false)⟩)
(.leaf ⟨125700,17,(.group 6 1091 false)⟩))))
(.branch 125785
(.branch 125751
(.branch 125734
(.leaf ⟨125717,17,(.group 6 1092 false)⟩)
(.leaf ⟨125734,17,(.group 6 1093 false)⟩))
(.branch 125768
(.leaf ⟨125751,17,(.group 6 1094 false)⟩)
(.leaf ⟨125768,17,(.group 6 1095 false)⟩)))
(.branch 125819
(.branch 125802
(.leaf ⟨125785,17,(.group 6 1096 false)⟩)
(.leaf ⟨125802,17,(.group 6 1097 false)⟩))
(.branch 125836
(.leaf ⟨125819,17,(.group 6 1098 false)⟩)
(.leaf ⟨125836,17,(.group 6 1099 false)⟩)))))
(.branch 125989
(.branch 125921
(.branch 125887
(.branch 125870
(.leaf ⟨125853,17,(.group 6 1100 false)⟩)
(.leaf ⟨125870,17,(.group 6 1101 false)⟩))
(.branch 125904
(.leaf ⟨125887,17,(.group 6 1102 false)⟩)
(.leaf ⟨125904,17,(.group 6 1103 false)⟩)))
(.branch 125955
(.branch 125938
(.leaf ⟨125921,17,(.group 6 1104 false)⟩)
(.leaf ⟨125938,17,(.group 6 1105 false)⟩))
(.branch 125972
(.leaf ⟨125955,17,(.group 6 1106 false)⟩)
(.leaf ⟨125972,17,(.group 6 1107 false)⟩))))
(.branch 126057
(.branch 126023
(.branch 126006
(.leaf ⟨125989,17,(.group 6 1108 false)⟩)
(.leaf ⟨126006,17,(.group 6 1109 false)⟩))
(.branch 126040
(.leaf ⟨126023,17,(.group 6 1110 false)⟩)
(.leaf ⟨126040,17,(.group 6 1111 false)⟩)))
(.branch 126091
(.branch 126074
(.leaf ⟨126057,17,(.group 6 1112 false)⟩)
(.leaf ⟨126074,17,(.group 6 1113 false)⟩))
(.branch 126108
(.leaf ⟨126091,17,(.group 6 1114 false)⟩)
(.leaf ⟨126108,17,(.group 6 1115 false)⟩))))))
(.branch 126397
(.branch 126261
(.branch 126193
(.branch 126159
(.branch 126142
(.leaf ⟨126125,17,(.group 6 1116 false)⟩)
(.leaf ⟨126142,17,(.group 6 1117 false)⟩))
(.branch 126176
(.leaf ⟨126159,17,(.group 6 1118 false)⟩)
(.leaf ⟨126176,17,(.group 6 1119 false)⟩)))
(.branch 126227
(.branch 126210
(.leaf ⟨126193,17,(.group 6 1120 false)⟩)
(.leaf ⟨126210,17,(.group 6 1121 false)⟩))
(.branch 126244
(.leaf ⟨126227,17,(.group 6 1122 false)⟩)
(.leaf ⟨126244,17,(.group 6 1123 false)⟩))))
(.branch 126329
(.branch 126295
(.branch 126278
(.leaf ⟨126261,17,(.group 6 1124 false)⟩)
(.leaf ⟨126278,17,(.group 6 1125 false)⟩))
(.branch 126312
(.leaf ⟨126295,17,(.group 6 1126 false)⟩)
(.leaf ⟨126312,17,(.group 6 1127 false)⟩)))
(.branch 126363
(.branch 126346
(.leaf ⟨126329,17,(.group 6 1128 false)⟩)
(.leaf ⟨126346,17,(.group 6 1129 false)⟩))
(.branch 126380
(.leaf ⟨126363,17,(.group 6 1130 false)⟩)
(.leaf ⟨126380,17,(.group 6 1131 false)⟩)))))
(.branch 126533
(.branch 126465
(.branch 126431
(.branch 126414
(.leaf ⟨126397,17,(.group 6 1132 false)⟩)
(.leaf ⟨126414,17,(.group 6 1133 false)⟩))
(.branch 126448
(.leaf ⟨126431,17,(.group 6 1134 false)⟩)
(.leaf ⟨126448,17,(.group 6 1135 false)⟩)))
(.branch 126499
(.branch 126482
(.leaf ⟨126465,17,(.group 6 1136 false)⟩)
(.leaf ⟨126482,17,(.group 6 1137 false)⟩))
(.branch 126516
(.leaf ⟨126499,17,(.group 6 1138 false)⟩)
(.leaf ⟨126516,17,(.group 6 1139 false)⟩))))
(.branch 126601
(.branch 126567
(.branch 126550
(.leaf ⟨126533,17,(.group 6 1140 false)⟩)
(.leaf ⟨126550,17,(.group 6 1141 false)⟩))
(.branch 126584
(.leaf ⟨126567,17,(.group 6 1142 false)⟩)
(.leaf ⟨126584,17,(.group 6 1143 false)⟩)))
(.branch 126635
(.branch 126618
(.leaf ⟨126601,17,(.group 6 1144 false)⟩)
(.leaf ⟨126618,17,(.group 6 1145 false)⟩))
(.branch 126652
(.leaf ⟨126635,17,(.group 6 1146 false)⟩)
(.leaf ⟨126652,17,(.group 6 1147 false)⟩)))))))

theorem tree127_checked : tree127.check 125581 126669 = true := by decide +kernel

def tree128 : Tree := (.branch 127213
(.branch 126941
(.branch 126805
(.branch 126737
(.branch 126703
(.branch 126686
(.leaf ⟨126669,17,(.group 6 1148 false)⟩)
(.leaf ⟨126686,17,(.group 6 1149 false)⟩))
(.branch 126720
(.leaf ⟨126703,17,(.group 6 1150 false)⟩)
(.leaf ⟨126720,17,(.group 6 1151 false)⟩)))
(.branch 126771
(.branch 126754
(.leaf ⟨126737,17,(.group 6 1152 false)⟩)
(.leaf ⟨126754,17,(.group 6 1153 false)⟩))
(.branch 126788
(.leaf ⟨126771,17,(.group 6 1154 false)⟩)
(.leaf ⟨126788,17,(.group 6 1155 false)⟩))))
(.branch 126873
(.branch 126839
(.branch 126822
(.leaf ⟨126805,17,(.group 6 1156 false)⟩)
(.leaf ⟨126822,17,(.group 6 1157 false)⟩))
(.branch 126856
(.leaf ⟨126839,17,(.group 6 1158 false)⟩)
(.leaf ⟨126856,17,(.group 6 1159 false)⟩)))
(.branch 126907
(.branch 126890
(.leaf ⟨126873,17,(.group 6 1160 false)⟩)
(.leaf ⟨126890,17,(.group 6 1161 false)⟩))
(.branch 126924
(.leaf ⟨126907,17,(.group 6 1162 false)⟩)
(.leaf ⟨126924,17,(.group 6 1163 false)⟩)))))
(.branch 127077
(.branch 127009
(.branch 126975
(.branch 126958
(.leaf ⟨126941,17,(.group 6 1164 false)⟩)
(.leaf ⟨126958,17,(.group 6 1165 false)⟩))
(.branch 126992
(.leaf ⟨126975,17,(.group 6 1166 false)⟩)
(.leaf ⟨126992,17,(.group 6 1167 false)⟩)))
(.branch 127043
(.branch 127026
(.leaf ⟨127009,17,(.group 6 1168 false)⟩)
(.leaf ⟨127026,17,(.group 6 1169 false)⟩))
(.branch 127060
(.leaf ⟨127043,17,(.group 6 1170 false)⟩)
(.leaf ⟨127060,17,(.group 6 1171 false)⟩))))
(.branch 127145
(.branch 127111
(.branch 127094
(.leaf ⟨127077,17,(.group 6 1172 false)⟩)
(.leaf ⟨127094,17,(.group 6 1173 false)⟩))
(.branch 127128
(.leaf ⟨127111,17,(.group 6 1174 false)⟩)
(.leaf ⟨127128,17,(.group 6 1175 false)⟩)))
(.branch 127179
(.branch 127162
(.leaf ⟨127145,17,(.group 6 1176 false)⟩)
(.leaf ⟨127162,17,(.group 6 1177 false)⟩))
(.branch 127196
(.leaf ⟨127179,17,(.group 6 1178 false)⟩)
(.leaf ⟨127196,17,(.group 6 1179 false)⟩))))))
(.branch 127485
(.branch 127349
(.branch 127281
(.branch 127247
(.branch 127230
(.leaf ⟨127213,17,(.group 6 1180 false)⟩)
(.leaf ⟨127230,17,(.group 6 1181 false)⟩))
(.branch 127264
(.leaf ⟨127247,17,(.group 6 1182 false)⟩)
(.leaf ⟨127264,17,(.group 6 1183 false)⟩)))
(.branch 127315
(.branch 127298
(.leaf ⟨127281,17,(.group 6 1184 false)⟩)
(.leaf ⟨127298,17,(.group 6 1185 false)⟩))
(.branch 127332
(.leaf ⟨127315,17,(.group 6 1186 false)⟩)
(.leaf ⟨127332,17,(.group 6 1187 false)⟩))))
(.branch 127417
(.branch 127383
(.branch 127366
(.leaf ⟨127349,17,(.group 6 1188 false)⟩)
(.leaf ⟨127366,17,(.group 6 1189 false)⟩))
(.branch 127400
(.leaf ⟨127383,17,(.group 6 1190 false)⟩)
(.leaf ⟨127400,17,(.group 6 1191 false)⟩)))
(.branch 127451
(.branch 127434
(.leaf ⟨127417,17,(.group 6 1192 false)⟩)
(.leaf ⟨127434,17,(.group 6 1193 false)⟩))
(.branch 127468
(.leaf ⟨127451,17,(.group 6 1194 false)⟩)
(.leaf ⟨127468,17,(.group 6 1195 false)⟩)))))
(.branch 127621
(.branch 127553
(.branch 127519
(.branch 127502
(.leaf ⟨127485,17,(.group 6 1196 false)⟩)
(.leaf ⟨127502,17,(.group 6 1197 false)⟩))
(.branch 127536
(.leaf ⟨127519,17,(.group 6 1198 false)⟩)
(.leaf ⟨127536,17,(.group 6 1199 false)⟩)))
(.branch 127587
(.branch 127570
(.leaf ⟨127553,17,(.group 6 1200 false)⟩)
(.leaf ⟨127570,17,(.group 6 1201 false)⟩))
(.branch 127604
(.leaf ⟨127587,17,(.group 6 1202 false)⟩)
(.leaf ⟨127604,17,(.group 6 1203 false)⟩))))
(.branch 127689
(.branch 127655
(.branch 127638
(.leaf ⟨127621,17,(.group 6 1204 false)⟩)
(.leaf ⟨127638,17,(.group 6 1205 false)⟩))
(.branch 127672
(.leaf ⟨127655,17,(.group 6 1206 false)⟩)
(.leaf ⟨127672,17,(.group 6 1207 false)⟩)))
(.branch 127723
(.branch 127706
(.leaf ⟨127689,17,(.group 6 1208 false)⟩)
(.leaf ⟨127706,17,(.group 6 1209 false)⟩))
(.branch 127740
(.leaf ⟨127723,17,(.group 6 1210 false)⟩)
(.leaf ⟨127740,17,(.group 6 1211 false)⟩)))))))

theorem tree128_checked : tree128.check 126669 127757 = true := by decide +kernel

def tree129 : Tree := (.branch 128301
(.branch 128029
(.branch 127893
(.branch 127825
(.branch 127791
(.branch 127774
(.leaf ⟨127757,17,(.group 6 1212 false)⟩)
(.leaf ⟨127774,17,(.group 6 1213 false)⟩))
(.branch 127808
(.leaf ⟨127791,17,(.group 6 1214 false)⟩)
(.leaf ⟨127808,17,(.group 6 1215 false)⟩)))
(.branch 127859
(.branch 127842
(.leaf ⟨127825,17,(.group 6 1216 false)⟩)
(.leaf ⟨127842,17,(.group 6 1217 false)⟩))
(.branch 127876
(.leaf ⟨127859,17,(.group 6 1218 false)⟩)
(.leaf ⟨127876,17,(.group 6 1219 false)⟩))))
(.branch 127961
(.branch 127927
(.branch 127910
(.leaf ⟨127893,17,(.group 6 1220 false)⟩)
(.leaf ⟨127910,17,(.group 6 1221 false)⟩))
(.branch 127944
(.leaf ⟨127927,17,(.group 6 1222 false)⟩)
(.leaf ⟨127944,17,(.group 6 1223 false)⟩)))
(.branch 127995
(.branch 127978
(.leaf ⟨127961,17,(.group 6 1224 false)⟩)
(.leaf ⟨127978,17,(.group 6 1225 false)⟩))
(.branch 128012
(.leaf ⟨127995,17,(.group 6 1226 false)⟩)
(.leaf ⟨128012,17,(.group 6 1227 false)⟩)))))
(.branch 128165
(.branch 128097
(.branch 128063
(.branch 128046
(.leaf ⟨128029,17,(.group 6 1228 false)⟩)
(.leaf ⟨128046,17,(.group 6 1229 false)⟩))
(.branch 128080
(.leaf ⟨128063,17,(.group 6 1230 false)⟩)
(.leaf ⟨128080,17,(.group 6 1231 false)⟩)))
(.branch 128131
(.branch 128114
(.leaf ⟨128097,17,(.group 6 1232 false)⟩)
(.leaf ⟨128114,17,(.group 6 1233 false)⟩))
(.branch 128148
(.leaf ⟨128131,17,(.group 6 1234 false)⟩)
(.leaf ⟨128148,17,(.group 6 1235 false)⟩))))
(.branch 128233
(.branch 128199
(.branch 128182
(.leaf ⟨128165,17,(.group 6 1236 false)⟩)
(.leaf ⟨128182,17,(.group 6 1237 false)⟩))
(.branch 128216
(.leaf ⟨128199,17,(.group 6 1238 false)⟩)
(.leaf ⟨128216,17,(.group 6 1239 false)⟩)))
(.branch 128267
(.branch 128250
(.leaf ⟨128233,17,(.group 6 1240 false)⟩)
(.leaf ⟨128250,17,(.group 6 1241 false)⟩))
(.branch 128284
(.leaf ⟨128267,17,(.group 6 1242 false)⟩)
(.leaf ⟨128284,17,(.group 6 1243 false)⟩))))))
(.branch 128573
(.branch 128437
(.branch 128369
(.branch 128335
(.branch 128318
(.leaf ⟨128301,17,(.group 6 1244 false)⟩)
(.leaf ⟨128318,17,(.group 6 1245 false)⟩))
(.branch 128352
(.leaf ⟨128335,17,(.group 6 1246 false)⟩)
(.leaf ⟨128352,17,(.group 6 1247 false)⟩)))
(.branch 128403
(.branch 128386
(.leaf ⟨128369,17,(.group 6 1248 false)⟩)
(.leaf ⟨128386,17,(.group 6 1249 false)⟩))
(.branch 128420
(.leaf ⟨128403,17,(.group 6 1250 false)⟩)
(.leaf ⟨128420,17,(.group 6 1251 false)⟩))))
(.branch 128505
(.branch 128471
(.branch 128454
(.leaf ⟨128437,17,(.group 6 1252 false)⟩)
(.leaf ⟨128454,17,(.group 6 1253 false)⟩))
(.branch 128488
(.leaf ⟨128471,17,(.group 6 1254 false)⟩)
(.leaf ⟨128488,17,(.group 6 1255 false)⟩)))
(.branch 128539
(.branch 128522
(.leaf ⟨128505,17,(.group 6 1256 false)⟩)
(.leaf ⟨128522,17,(.group 6 1257 false)⟩))
(.branch 128556
(.leaf ⟨128539,17,(.group 6 1258 false)⟩)
(.leaf ⟨128556,17,(.group 6 1259 false)⟩)))))
(.branch 128709
(.branch 128641
(.branch 128607
(.branch 128590
(.leaf ⟨128573,17,(.group 6 1260 false)⟩)
(.leaf ⟨128590,17,(.group 6 1261 false)⟩))
(.branch 128624
(.leaf ⟨128607,17,(.group 6 1262 false)⟩)
(.leaf ⟨128624,17,(.group 6 1263 false)⟩)))
(.branch 128675
(.branch 128658
(.leaf ⟨128641,17,(.group 6 1264 false)⟩)
(.leaf ⟨128658,17,(.group 6 1265 false)⟩))
(.branch 128692
(.leaf ⟨128675,17,(.group 6 1266 false)⟩)
(.leaf ⟨128692,17,(.group 6 1267 false)⟩))))
(.branch 128777
(.branch 128743
(.branch 128726
(.leaf ⟨128709,17,(.group 6 1268 false)⟩)
(.leaf ⟨128726,17,(.group 6 1269 false)⟩))
(.branch 128760
(.leaf ⟨128743,17,(.group 6 1270 false)⟩)
(.leaf ⟨128760,17,(.group 6 1271 false)⟩)))
(.branch 128811
(.branch 128794
(.leaf ⟨128777,17,(.group 6 1272 false)⟩)
(.leaf ⟨128794,17,(.group 6 1273 false)⟩))
(.branch 128828
(.leaf ⟨128811,17,(.group 6 1274 false)⟩)
(.leaf ⟨128828,17,(.group 6 1275 false)⟩)))))))

theorem tree129_checked : tree129.check 127757 128845 = true := by decide +kernel

def tree130 : Tree := (.branch 129389
(.branch 129117
(.branch 128981
(.branch 128913
(.branch 128879
(.branch 128862
(.leaf ⟨128845,17,(.group 6 1276 false)⟩)
(.leaf ⟨128862,17,(.group 6 1277 false)⟩))
(.branch 128896
(.leaf ⟨128879,17,(.group 6 1278 false)⟩)
(.leaf ⟨128896,17,(.group 6 1279 false)⟩)))
(.branch 128947
(.branch 128930
(.leaf ⟨128913,17,(.group 6 1280 false)⟩)
(.leaf ⟨128930,17,(.group 6 1281 false)⟩))
(.branch 128964
(.leaf ⟨128947,17,(.group 6 1282 false)⟩)
(.leaf ⟨128964,17,(.group 6 1283 false)⟩))))
(.branch 129049
(.branch 129015
(.branch 128998
(.leaf ⟨128981,17,(.group 6 1284 false)⟩)
(.leaf ⟨128998,17,(.group 6 1285 false)⟩))
(.branch 129032
(.leaf ⟨129015,17,(.group 6 1286 false)⟩)
(.leaf ⟨129032,17,(.group 6 1287 false)⟩)))
(.branch 129083
(.branch 129066
(.leaf ⟨129049,17,(.group 6 1288 false)⟩)
(.leaf ⟨129066,17,(.group 6 1289 false)⟩))
(.branch 129100
(.leaf ⟨129083,17,(.group 6 1290 false)⟩)
(.leaf ⟨129100,17,(.group 6 1291 false)⟩)))))
(.branch 129253
(.branch 129185
(.branch 129151
(.branch 129134
(.leaf ⟨129117,17,(.group 6 1292 false)⟩)
(.leaf ⟨129134,17,(.group 6 1293 false)⟩))
(.branch 129168
(.leaf ⟨129151,17,(.group 6 1294 false)⟩)
(.leaf ⟨129168,17,(.group 6 1295 false)⟩)))
(.branch 129219
(.branch 129202
(.leaf ⟨129185,17,(.group 6 1296 false)⟩)
(.leaf ⟨129202,17,(.group 6 1297 false)⟩))
(.branch 129236
(.leaf ⟨129219,17,(.group 6 1298 false)⟩)
(.leaf ⟨129236,17,(.group 6 1299 false)⟩))))
(.branch 129321
(.branch 129287
(.branch 129270
(.leaf ⟨129253,17,(.group 6 1300 false)⟩)
(.leaf ⟨129270,17,(.group 6 1301 false)⟩))
(.branch 129304
(.leaf ⟨129287,17,(.group 7 253 false)⟩)
(.leaf ⟨129304,17,(.group 7 254 false)⟩)))
(.branch 129355
(.branch 129338
(.leaf ⟨129321,17,(.group 7 255 false)⟩)
(.leaf ⟨129338,17,(.group 7 256 false)⟩))
(.branch 129372
(.leaf ⟨129355,17,(.group 7 257 false)⟩)
(.leaf ⟨129372,17,(.group 7 258 false)⟩))))))
(.branch 129661
(.branch 129525
(.branch 129457
(.branch 129423
(.branch 129406
(.leaf ⟨129389,17,(.group 7 259 false)⟩)
(.leaf ⟨129406,17,(.group 7 260 false)⟩))
(.branch 129440
(.leaf ⟨129423,17,(.group 7 261 false)⟩)
(.leaf ⟨129440,17,(.group 7 262 false)⟩)))
(.branch 129491
(.branch 129474
(.leaf ⟨129457,17,(.group 7 263 false)⟩)
(.leaf ⟨129474,17,(.group 7 264 false)⟩))
(.branch 129508
(.leaf ⟨129491,17,(.group 7 265 false)⟩)
(.leaf ⟨129508,17,(.group 7 266 false)⟩))))
(.branch 129593
(.branch 129559
(.branch 129542
(.leaf ⟨129525,17,(.group 7 267 false)⟩)
(.leaf ⟨129542,17,(.group 7 268 false)⟩))
(.branch 129576
(.leaf ⟨129559,17,(.group 7 269 false)⟩)
(.leaf ⟨129576,17,(.group 7 270 false)⟩)))
(.branch 129627
(.branch 129610
(.leaf ⟨129593,17,(.group 7 271 false)⟩)
(.leaf ⟨129610,17,(.group 7 272 false)⟩))
(.branch 129644
(.leaf ⟨129627,17,(.group 7 273 false)⟩)
(.leaf ⟨129644,17,(.group 7 274 false)⟩)))))
(.branch 129797
(.branch 129729
(.branch 129695
(.branch 129678
(.leaf ⟨129661,17,(.group 7 275 false)⟩)
(.leaf ⟨129678,17,(.group 7 276 false)⟩))
(.branch 129712
(.leaf ⟨129695,17,(.group 7 277 false)⟩)
(.leaf ⟨129712,17,(.group 7 278 false)⟩)))
(.branch 129763
(.branch 129746
(.leaf ⟨129729,17,(.group 7 279 false)⟩)
(.leaf ⟨129746,17,(.group 7 280 false)⟩))
(.branch 129780
(.leaf ⟨129763,17,(.group 7 281 false)⟩)
(.leaf ⟨129780,17,(.group 7 282 false)⟩))))
(.branch 129865
(.branch 129831
(.branch 129814
(.leaf ⟨129797,17,(.group 7 283 false)⟩)
(.leaf ⟨129814,17,(.group 7 284 false)⟩))
(.branch 129848
(.leaf ⟨129831,17,(.group 7 285 false)⟩)
(.leaf ⟨129848,17,(.group 7 286 false)⟩)))
(.branch 129899
(.branch 129882
(.leaf ⟨129865,17,(.group 7 287 false)⟩)
(.leaf ⟨129882,17,(.group 7 288 false)⟩))
(.branch 129916
(.leaf ⟨129899,17,(.group 7 289 false)⟩)
(.leaf ⟨129916,17,(.group 7 290 false)⟩)))))))

theorem tree130_checked : tree130.check 128845 129933 = true := by decide +kernel

def tree131 : Tree := (.branch 130477
(.branch 130205
(.branch 130069
(.branch 130001
(.branch 129967
(.branch 129950
(.leaf ⟨129933,17,(.group 7 291 false)⟩)
(.leaf ⟨129950,17,(.group 7 292 false)⟩))
(.branch 129984
(.leaf ⟨129967,17,(.group 7 293 false)⟩)
(.leaf ⟨129984,17,(.group 7 294 false)⟩)))
(.branch 130035
(.branch 130018
(.leaf ⟨130001,17,(.group 7 295 false)⟩)
(.leaf ⟨130018,17,(.group 7 296 false)⟩))
(.branch 130052
(.leaf ⟨130035,17,(.group 7 297 false)⟩)
(.leaf ⟨130052,17,(.group 7 298 false)⟩))))
(.branch 130137
(.branch 130103
(.branch 130086
(.leaf ⟨130069,17,(.group 7 299 false)⟩)
(.leaf ⟨130086,17,(.group 7 300 false)⟩))
(.branch 130120
(.leaf ⟨130103,17,(.group 7 301 false)⟩)
(.leaf ⟨130120,17,(.group 7 302 false)⟩)))
(.branch 130171
(.branch 130154
(.leaf ⟨130137,17,(.group 7 303 false)⟩)
(.leaf ⟨130154,17,(.group 7 304 false)⟩))
(.branch 130188
(.leaf ⟨130171,17,(.group 7 305 false)⟩)
(.leaf ⟨130188,17,(.group 7 306 false)⟩)))))
(.branch 130341
(.branch 130273
(.branch 130239
(.branch 130222
(.leaf ⟨130205,17,(.group 7 307 false)⟩)
(.leaf ⟨130222,17,(.group 7 308 false)⟩))
(.branch 130256
(.leaf ⟨130239,17,(.group 7 309 false)⟩)
(.leaf ⟨130256,17,(.group 7 310 false)⟩)))
(.branch 130307
(.branch 130290
(.leaf ⟨130273,17,(.group 7 311 false)⟩)
(.leaf ⟨130290,17,(.group 7 312 false)⟩))
(.branch 130324
(.leaf ⟨130307,17,(.group 7 313 false)⟩)
(.leaf ⟨130324,17,(.group 7 314 false)⟩))))
(.branch 130409
(.branch 130375
(.branch 130358
(.leaf ⟨130341,17,(.group 7 315 false)⟩)
(.leaf ⟨130358,17,(.group 7 316 false)⟩))
(.branch 130392
(.leaf ⟨130375,17,(.group 7 317 false)⟩)
(.leaf ⟨130392,17,(.group 7 318 false)⟩)))
(.branch 130443
(.branch 130426
(.leaf ⟨130409,17,(.group 8 326 false)⟩)
(.leaf ⟨130426,17,(.group 8 327 false)⟩))
(.branch 130460
(.leaf ⟨130443,17,(.group 8 328 false)⟩)
(.leaf ⟨130460,17,(.group 8 329 false)⟩))))))
(.branch 130749
(.branch 130613
(.branch 130545
(.branch 130511
(.branch 130494
(.leaf ⟨130477,17,(.group 8 330 false)⟩)
(.leaf ⟨130494,17,(.group 8 331 false)⟩))
(.branch 130528
(.leaf ⟨130511,17,(.group 8 332 false)⟩)
(.leaf ⟨130528,17,(.group 8 333 false)⟩)))
(.branch 130579
(.branch 130562
(.leaf ⟨130545,17,(.group 8 334 false)⟩)
(.leaf ⟨130562,17,(.group 8 335 false)⟩))
(.branch 130596
(.leaf ⟨130579,17,(.group 8 336 false)⟩)
(.leaf ⟨130596,17,(.group 8 337 false)⟩))))
(.branch 130681
(.branch 130647
(.branch 130630
(.leaf ⟨130613,17,(.group 8 338 false)⟩)
(.leaf ⟨130630,17,(.group 8 339 false)⟩))
(.branch 130664
(.leaf ⟨130647,17,(.group 8 340 false)⟩)
(.leaf ⟨130664,17,(.group 8 341 false)⟩)))
(.branch 130715
(.branch 130698
(.leaf ⟨130681,17,(.group 8 342 false)⟩)
(.leaf ⟨130698,17,(.group 8 343 false)⟩))
(.branch 130732
(.leaf ⟨130715,17,(.group 8 344 false)⟩)
(.leaf ⟨130732,17,(.group 8 345 false)⟩)))))
(.branch 130885
(.branch 130817
(.branch 130783
(.branch 130766
(.leaf ⟨130749,17,(.group 8 346 false)⟩)
(.leaf ⟨130766,17,(.group 8 347 false)⟩))
(.branch 130800
(.leaf ⟨130783,17,(.group 8 348 false)⟩)
(.leaf ⟨130800,17,(.group 8 349 false)⟩)))
(.branch 130851
(.branch 130834
(.leaf ⟨130817,17,(.group 8 350 false)⟩)
(.leaf ⟨130834,17,(.group 8 351 false)⟩))
(.branch 130868
(.leaf ⟨130851,17,(.group 8 352 false)⟩)
(.leaf ⟨130868,17,(.group 8 353 false)⟩))))
(.branch 130953
(.branch 130919
(.branch 130902
(.leaf ⟨130885,17,(.group 8 354 false)⟩)
(.leaf ⟨130902,17,(.group 8 355 false)⟩))
(.branch 130936
(.leaf ⟨130919,17,(.group 8 356 false)⟩)
(.leaf ⟨130936,17,(.group 8 357 false)⟩)))
(.branch 130987
(.branch 130970
(.leaf ⟨130953,17,(.group 8 358 false)⟩)
(.leaf ⟨130970,17,(.group 8 359 false)⟩))
(.branch 131004
(.leaf ⟨130987,17,(.group 8 360 false)⟩)
(.leaf ⟨131004,17,(.group 8 361 false)⟩)))))))

theorem tree131_checked : tree131.check 129933 131021 = true := by decide +kernel

def tree132 : Tree := (.branch 131565
(.branch 131293
(.branch 131157
(.branch 131089
(.branch 131055
(.branch 131038
(.leaf ⟨131021,17,(.group 8 362 false)⟩)
(.leaf ⟨131038,17,(.group 8 363 false)⟩))
(.branch 131072
(.leaf ⟨131055,17,(.group 8 364 false)⟩)
(.leaf ⟨131072,17,(.group 8 365 false)⟩)))
(.branch 131123
(.branch 131106
(.leaf ⟨131089,17,(.group 8 366 false)⟩)
(.leaf ⟨131106,17,(.group 8 367 false)⟩))
(.branch 131140
(.leaf ⟨131123,17,(.group 8 368 false)⟩)
(.leaf ⟨131140,17,(.group 8 369 false)⟩))))
(.branch 131225
(.branch 131191
(.branch 131174
(.leaf ⟨131157,17,(.group 8 370 false)⟩)
(.leaf ⟨131174,17,(.group 8 371 false)⟩))
(.branch 131208
(.leaf ⟨131191,17,(.group 8 372 false)⟩)
(.leaf ⟨131208,17,(.group 8 373 false)⟩)))
(.branch 131259
(.branch 131242
(.leaf ⟨131225,17,(.group 8 374 false)⟩)
(.leaf ⟨131242,17,(.group 8 375 false)⟩))
(.branch 131276
(.leaf ⟨131259,17,(.group 8 376 false)⟩)
(.leaf ⟨131276,17,(.group 8 377 false)⟩)))))
(.branch 131429
(.branch 131361
(.branch 131327
(.branch 131310
(.leaf ⟨131293,17,(.group 8 378 false)⟩)
(.leaf ⟨131310,17,(.group 8 379 false)⟩))
(.branch 131344
(.leaf ⟨131327,17,(.group 8 380 false)⟩)
(.leaf ⟨131344,17,(.group 8 381 false)⟩)))
(.branch 131395
(.branch 131378
(.leaf ⟨131361,17,(.group 8 382 false)⟩)
(.leaf ⟨131378,17,(.group 8 383 false)⟩))
(.branch 131412
(.leaf ⟨131395,17,(.group 8 384 false)⟩)
(.leaf ⟨131412,17,(.group 8 385 false)⟩))))
(.branch 131497
(.branch 131463
(.branch 131446
(.leaf ⟨131429,17,(.group 8 386 false)⟩)
(.leaf ⟨131446,17,(.group 8 387 false)⟩))
(.branch 131480
(.leaf ⟨131463,17,(.group 8 388 false)⟩)
(.leaf ⟨131480,17,(.group 8 389 false)⟩)))
(.branch 131531
(.branch 131514
(.leaf ⟨131497,17,(.group 8 390 false)⟩)
(.leaf ⟨131514,17,(.group 8 391 false)⟩))
(.branch 131548
(.leaf ⟨131531,17,(.group 8 392 false)⟩)
(.leaf ⟨131548,17,(.group 8 393 false)⟩))))))
(.branch 131852
(.branch 131708
(.branch 131636
(.branch 131600
(.branch 131582
(.leaf ⟨131565,17,(.group 8 394 false)⟩)
(.leaf ⟨131582,18,(.group 0 726 false)⟩))
(.branch 131618
(.leaf ⟨131600,18,(.group 0 727 false)⟩)
(.leaf ⟨131618,18,(.group 0 728 false)⟩)))
(.branch 131672
(.branch 131654
(.leaf ⟨131636,18,(.group 0 729 false)⟩)
(.leaf ⟨131654,18,(.group 0 730 false)⟩))
(.branch 131690
(.leaf ⟨131672,18,(.group 0 731 false)⟩)
(.leaf ⟨131690,18,(.group 0 732 false)⟩))))
(.branch 131780
(.branch 131744
(.branch 131726
(.leaf ⟨131708,18,(.group 0 733 false)⟩)
(.leaf ⟨131726,18,(.group 0 734 false)⟩))
(.branch 131762
(.leaf ⟨131744,18,(.group 0 735 false)⟩)
(.leaf ⟨131762,18,(.group 0 736 false)⟩)))
(.branch 131816
(.branch 131798
(.leaf ⟨131780,18,(.group 0 737 false)⟩)
(.leaf ⟨131798,18,(.group 0 738 false)⟩))
(.branch 131834
(.leaf ⟨131816,18,(.group 0 739 false)⟩)
(.leaf ⟨131834,18,(.group 0 740 false)⟩)))))
(.branch 131996
(.branch 131924
(.branch 131888
(.branch 131870
(.leaf ⟨131852,18,(.group 0 741 false)⟩)
(.leaf ⟨131870,18,(.group 0 742 false)⟩))
(.branch 131906
(.leaf ⟨131888,18,(.group 0 743 false)⟩)
(.leaf ⟨131906,18,(.group 0 744 false)⟩)))
(.branch 131960
(.branch 131942
(.leaf ⟨131924,18,(.group 0 745 false)⟩)
(.leaf ⟨131942,18,(.group 0 746 false)⟩))
(.branch 131978
(.leaf ⟨131960,18,(.group 0 747 false)⟩)
(.leaf ⟨131978,18,(.group 0 748 false)⟩))))
(.branch 132068
(.branch 132032
(.branch 132014
(.leaf ⟨131996,18,(.group 0 749 false)⟩)
(.leaf ⟨132014,18,(.group 0 750 false)⟩))
(.branch 132050
(.leaf ⟨132032,18,(.group 0 751 false)⟩)
(.leaf ⟨132050,18,(.group 0 752 false)⟩)))
(.branch 132104
(.branch 132086
(.leaf ⟨132068,18,(.group 0 753 false)⟩)
(.leaf ⟨132086,18,(.group 0 754 false)⟩))
(.branch 132122
(.leaf ⟨132104,18,(.group 0 755 false)⟩)
(.leaf ⟨132122,18,(.group 0 756 false)⟩)))))))

theorem tree132_checked : tree132.check 131021 132140 = true := by decide +kernel

def tree133 : Tree := (.branch 132716
(.branch 132428
(.branch 132284
(.branch 132212
(.branch 132176
(.branch 132158
(.leaf ⟨132140,18,(.group 0 757 false)⟩)
(.leaf ⟨132158,18,(.group 0 758 false)⟩))
(.branch 132194
(.leaf ⟨132176,18,(.group 0 759 false)⟩)
(.leaf ⟨132194,18,(.group 0 760 false)⟩)))
(.branch 132248
(.branch 132230
(.leaf ⟨132212,18,(.group 0 761 false)⟩)
(.leaf ⟨132230,18,(.group 0 762 false)⟩))
(.branch 132266
(.leaf ⟨132248,18,(.group 0 763 false)⟩)
(.leaf ⟨132266,18,(.group 0 764 false)⟩))))
(.branch 132356
(.branch 132320
(.branch 132302
(.leaf ⟨132284,18,(.group 0 765 false)⟩)
(.leaf ⟨132302,18,(.group 0 766 false)⟩))
(.branch 132338
(.leaf ⟨132320,18,(.group 0 767 false)⟩)
(.leaf ⟨132338,18,(.group 0 768 false)⟩)))
(.branch 132392
(.branch 132374
(.leaf ⟨132356,18,(.group 0 769 false)⟩)
(.leaf ⟨132374,18,(.group 0 770 false)⟩))
(.branch 132410
(.leaf ⟨132392,18,(.group 0 771 false)⟩)
(.leaf ⟨132410,18,(.group 0 772 false)⟩)))))
(.branch 132572
(.branch 132500
(.branch 132464
(.branch 132446
(.leaf ⟨132428,18,(.group 0 773 false)⟩)
(.leaf ⟨132446,18,(.group 0 774 false)⟩))
(.branch 132482
(.leaf ⟨132464,18,(.group 0 775 false)⟩)
(.leaf ⟨132482,18,(.group 0 776 false)⟩)))
(.branch 132536
(.branch 132518
(.leaf ⟨132500,18,(.group 0 777 false)⟩)
(.leaf ⟨132518,18,(.group 0 778 false)⟩))
(.branch 132554
(.leaf ⟨132536,18,(.group 0 779 false)⟩)
(.leaf ⟨132554,18,(.group 0 780 false)⟩))))
(.branch 132644
(.branch 132608
(.branch 132590
(.leaf ⟨132572,18,(.group 0 781 false)⟩)
(.leaf ⟨132590,18,(.group 0 782 false)⟩))
(.branch 132626
(.leaf ⟨132608,18,(.group 0 783 false)⟩)
(.leaf ⟨132626,18,(.group 0 784 false)⟩)))
(.branch 132680
(.branch 132662
(.leaf ⟨132644,18,(.group 0 785 false)⟩)
(.leaf ⟨132662,18,(.group 0 786 false)⟩))
(.branch 132698
(.leaf ⟨132680,18,(.group 0 787 false)⟩)
(.leaf ⟨132698,18,(.group 0 788 false)⟩))))))
(.branch 133004
(.branch 132860
(.branch 132788
(.branch 132752
(.branch 132734
(.leaf ⟨132716,18,(.group 0 789 false)⟩)
(.leaf ⟨132734,18,(.group 0 790 false)⟩))
(.branch 132770
(.leaf ⟨132752,18,(.group 0 791 false)⟩)
(.leaf ⟨132770,18,(.group 0 792 false)⟩)))
(.branch 132824
(.branch 132806
(.leaf ⟨132788,18,(.group 0 793 false)⟩)
(.leaf ⟨132806,18,(.group 0 794 false)⟩))
(.branch 132842
(.leaf ⟨132824,18,(.group 0 795 false)⟩)
(.leaf ⟨132842,18,(.group 0 796 false)⟩))))
(.branch 132932
(.branch 132896
(.branch 132878
(.leaf ⟨132860,18,(.group 0 797 false)⟩)
(.leaf ⟨132878,18,(.group 0 798 false)⟩))
(.branch 132914
(.leaf ⟨132896,18,(.group 0 799 false)⟩)
(.leaf ⟨132914,18,(.group 0 800 false)⟩)))
(.branch 132968
(.branch 132950
(.leaf ⟨132932,18,(.group 0 801 false)⟩)
(.leaf ⟨132950,18,(.group 0 802 false)⟩))
(.branch 132986
(.leaf ⟨132968,18,(.group 0 803 false)⟩)
(.leaf ⟨132986,18,(.group 0 804 false)⟩)))))
(.branch 133148
(.branch 133076
(.branch 133040
(.branch 133022
(.leaf ⟨133004,18,(.group 0 805 false)⟩)
(.leaf ⟨133022,18,(.group 0 806 false)⟩))
(.branch 133058
(.leaf ⟨133040,18,(.group 0 807 false)⟩)
(.leaf ⟨133058,18,(.group 0 808 false)⟩)))
(.branch 133112
(.branch 133094
(.leaf ⟨133076,18,(.group 0 809 false)⟩)
(.leaf ⟨133094,18,(.group 0 810 false)⟩))
(.branch 133130
(.leaf ⟨133112,18,(.group 0 811 false)⟩)
(.leaf ⟨133130,18,(.group 0 812 false)⟩))))
(.branch 133220
(.branch 133184
(.branch 133166
(.leaf ⟨133148,18,(.group 0 813 false)⟩)
(.leaf ⟨133166,18,(.group 0 814 false)⟩))
(.branch 133202
(.leaf ⟨133184,18,(.group 0 815 false)⟩)
(.leaf ⟨133202,18,(.group 0 816 false)⟩)))
(.branch 133256
(.branch 133238
(.leaf ⟨133220,18,(.group 0 817 false)⟩)
(.leaf ⟨133238,18,(.group 0 818 false)⟩))
(.branch 133274
(.leaf ⟨133256,18,(.group 0 819 false)⟩)
(.leaf ⟨133274,18,(.group 0 820 false)⟩)))))))

theorem tree133_checked : tree133.check 132140 133292 = true := by decide +kernel

def tree134 : Tree := (.branch 133868
(.branch 133580
(.branch 133436
(.branch 133364
(.branch 133328
(.branch 133310
(.leaf ⟨133292,18,(.group 0 821 false)⟩)
(.leaf ⟨133310,18,(.group 0 822 false)⟩))
(.branch 133346
(.leaf ⟨133328,18,(.group 0 823 false)⟩)
(.leaf ⟨133346,18,(.group 0 824 false)⟩)))
(.branch 133400
(.branch 133382
(.leaf ⟨133364,18,(.group 0 825 false)⟩)
(.leaf ⟨133382,18,(.group 0 826 false)⟩))
(.branch 133418
(.leaf ⟨133400,18,(.group 0 827 false)⟩)
(.leaf ⟨133418,18,(.group 0 828 false)⟩))))
(.branch 133508
(.branch 133472
(.branch 133454
(.leaf ⟨133436,18,(.group 0 829 false)⟩)
(.leaf ⟨133454,18,(.group 0 830 false)⟩))
(.branch 133490
(.leaf ⟨133472,18,(.group 0 831 false)⟩)
(.leaf ⟨133490,18,(.group 0 832 false)⟩)))
(.branch 133544
(.branch 133526
(.leaf ⟨133508,18,(.group 0 833 false)⟩)
(.leaf ⟨133526,18,(.group 0 834 false)⟩))
(.branch 133562
(.leaf ⟨133544,18,(.group 0 835 false)⟩)
(.leaf ⟨133562,18,(.group 0 836 false)⟩)))))
(.branch 133724
(.branch 133652
(.branch 133616
(.branch 133598
(.leaf ⟨133580,18,(.group 0 837 false)⟩)
(.leaf ⟨133598,18,(.group 0 838 false)⟩))
(.branch 133634
(.leaf ⟨133616,18,(.group 0 839 false)⟩)
(.leaf ⟨133634,18,(.group 0 840 false)⟩)))
(.branch 133688
(.branch 133670
(.leaf ⟨133652,18,(.group 0 841 false)⟩)
(.leaf ⟨133670,18,(.group 0 842 false)⟩))
(.branch 133706
(.leaf ⟨133688,18,(.group 0 843 false)⟩)
(.leaf ⟨133706,18,(.group 0 844 false)⟩))))
(.branch 133796
(.branch 133760
(.branch 133742
(.leaf ⟨133724,18,(.group 0 845 false)⟩)
(.leaf ⟨133742,18,(.group 0 846 false)⟩))
(.branch 133778
(.leaf ⟨133760,18,(.group 0 847 false)⟩)
(.leaf ⟨133778,18,(.group 0 848 false)⟩)))
(.branch 133832
(.branch 133814
(.leaf ⟨133796,18,(.group 0 849 false)⟩)
(.leaf ⟨133814,18,(.group 0 850 false)⟩))
(.branch 133850
(.leaf ⟨133832,18,(.group 0 851 false)⟩)
(.leaf ⟨133850,18,(.group 0 852 false)⟩))))))
(.branch 134156
(.branch 134012
(.branch 133940
(.branch 133904
(.branch 133886
(.leaf ⟨133868,18,(.group 0 853 false)⟩)
(.leaf ⟨133886,18,(.group 0 854 false)⟩))
(.branch 133922
(.leaf ⟨133904,18,(.group 0 855 false)⟩)
(.leaf ⟨133922,18,(.group 0 856 false)⟩)))
(.branch 133976
(.branch 133958
(.leaf ⟨133940,18,(.group 0 857 false)⟩)
(.leaf ⟨133958,18,(.group 0 858 false)⟩))
(.branch 133994
(.leaf ⟨133976,18,(.group 0 859 false)⟩)
(.leaf ⟨133994,18,(.group 0 860 false)⟩))))
(.branch 134084
(.branch 134048
(.branch 134030
(.leaf ⟨134012,18,(.group 0 861 false)⟩)
(.leaf ⟨134030,18,(.group 0 862 false)⟩))
(.branch 134066
(.leaf ⟨134048,18,(.group 0 863 false)⟩)
(.leaf ⟨134066,18,(.group 0 864 false)⟩)))
(.branch 134120
(.branch 134102
(.leaf ⟨134084,18,(.group 0 865 false)⟩)
(.leaf ⟨134102,18,(.group 0 866 false)⟩))
(.branch 134138
(.leaf ⟨134120,18,(.group 0 867 false)⟩)
(.leaf ⟨134138,18,(.group 0 868 false)⟩)))))
(.branch 134300
(.branch 134228
(.branch 134192
(.branch 134174
(.leaf ⟨134156,18,(.group 0 869 false)⟩)
(.leaf ⟨134174,18,(.group 0 870 false)⟩))
(.branch 134210
(.leaf ⟨134192,18,(.group 0 871 false)⟩)
(.leaf ⟨134210,18,(.group 0 872 false)⟩)))
(.branch 134264
(.branch 134246
(.leaf ⟨134228,18,(.group 0 873 false)⟩)
(.leaf ⟨134246,18,(.group 0 874 false)⟩))
(.branch 134282
(.leaf ⟨134264,18,(.group 0 875 false)⟩)
(.leaf ⟨134282,18,(.group 0 876 false)⟩))))
(.branch 134372
(.branch 134336
(.branch 134318
(.leaf ⟨134300,18,(.group 0 877 false)⟩)
(.leaf ⟨134318,18,(.group 0 878 false)⟩))
(.branch 134354
(.leaf ⟨134336,18,(.group 0 879 false)⟩)
(.leaf ⟨134354,18,(.group 0 880 false)⟩)))
(.branch 134408
(.branch 134390
(.leaf ⟨134372,18,(.group 0 881 false)⟩)
(.leaf ⟨134390,18,(.group 0 882 false)⟩))
(.branch 134426
(.leaf ⟨134408,18,(.group 0 883 false)⟩)
(.leaf ⟨134426,18,(.group 0 884 false)⟩)))))))

theorem tree134_checked : tree134.check 133292 134444 = true := by decide +kernel

def tree135 : Tree := (.branch 135020
(.branch 134732
(.branch 134588
(.branch 134516
(.branch 134480
(.branch 134462
(.leaf ⟨134444,18,(.group 0 885 false)⟩)
(.leaf ⟨134462,18,(.group 0 886 false)⟩))
(.branch 134498
(.leaf ⟨134480,18,(.group 0 887 false)⟩)
(.leaf ⟨134498,18,(.group 0 888 false)⟩)))
(.branch 134552
(.branch 134534
(.leaf ⟨134516,18,(.group 0 889 false)⟩)
(.leaf ⟨134534,18,(.group 0 890 false)⟩))
(.branch 134570
(.leaf ⟨134552,18,(.group 0 891 false)⟩)
(.leaf ⟨134570,18,(.group 0 892 false)⟩))))
(.branch 134660
(.branch 134624
(.branch 134606
(.leaf ⟨134588,18,(.group 0 893 false)⟩)
(.leaf ⟨134606,18,(.group 0 894 false)⟩))
(.branch 134642
(.leaf ⟨134624,18,(.group 0 895 false)⟩)
(.leaf ⟨134642,18,(.group 0 896 false)⟩)))
(.branch 134696
(.branch 134678
(.leaf ⟨134660,18,(.group 0 897 false)⟩)
(.leaf ⟨134678,18,(.group 0 898 false)⟩))
(.branch 134714
(.leaf ⟨134696,18,(.group 0 899 false)⟩)
(.leaf ⟨134714,18,(.group 0 900 false)⟩)))))
(.branch 134876
(.branch 134804
(.branch 134768
(.branch 134750
(.leaf ⟨134732,18,(.group 0 901 false)⟩)
(.leaf ⟨134750,18,(.group 0 902 false)⟩))
(.branch 134786
(.leaf ⟨134768,18,(.group 0 903 false)⟩)
(.leaf ⟨134786,18,(.group 0 904 false)⟩)))
(.branch 134840
(.branch 134822
(.leaf ⟨134804,18,(.group 0 905 false)⟩)
(.leaf ⟨134822,18,(.group 0 906 false)⟩))
(.branch 134858
(.leaf ⟨134840,18,(.group 0 907 false)⟩)
(.leaf ⟨134858,18,(.group 1 286 false)⟩))))
(.branch 134948
(.branch 134912
(.branch 134894
(.leaf ⟨134876,18,(.group 1 287 false)⟩)
(.leaf ⟨134894,18,(.group 1 288 false)⟩))
(.branch 134930
(.leaf ⟨134912,18,(.group 1 289 false)⟩)
(.leaf ⟨134930,18,(.group 1 290 false)⟩)))
(.branch 134984
(.branch 134966
(.leaf ⟨134948,18,(.group 1 291 false)⟩)
(.leaf ⟨134966,18,(.group 1 292 false)⟩))
(.branch 135002
(.leaf ⟨134984,18,(.group 1 293 false)⟩)
(.leaf ⟨135002,18,(.group 1 294 false)⟩))))))
(.branch 135308
(.branch 135164
(.branch 135092
(.branch 135056
(.branch 135038
(.leaf ⟨135020,18,(.group 1 295 false)⟩)
(.leaf ⟨135038,18,(.group 1 296 false)⟩))
(.branch 135074
(.leaf ⟨135056,18,(.group 1 297 false)⟩)
(.leaf ⟨135074,18,(.group 1 298 false)⟩)))
(.branch 135128
(.branch 135110
(.leaf ⟨135092,18,(.group 1 299 false)⟩)
(.leaf ⟨135110,18,(.group 1 300 false)⟩))
(.branch 135146
(.leaf ⟨135128,18,(.group 1 301 false)⟩)
(.leaf ⟨135146,18,(.group 1 302 false)⟩))))
(.branch 135236
(.branch 135200
(.branch 135182
(.leaf ⟨135164,18,(.group 1 303 false)⟩)
(.leaf ⟨135182,18,(.group 1 304 false)⟩))
(.branch 135218
(.leaf ⟨135200,18,(.group 1 305 false)⟩)
(.leaf ⟨135218,18,(.group 1 306 false)⟩)))
(.branch 135272
(.branch 135254
(.leaf ⟨135236,18,(.group 1 307 false)⟩)
(.leaf ⟨135254,18,(.group 1 308 false)⟩))
(.branch 135290
(.leaf ⟨135272,18,(.group 1 309 false)⟩)
(.leaf ⟨135290,18,(.group 1 310 false)⟩)))))
(.branch 135452
(.branch 135380
(.branch 135344
(.branch 135326
(.leaf ⟨135308,18,(.group 1 311 false)⟩)
(.leaf ⟨135326,18,(.group 1 312 false)⟩))
(.branch 135362
(.leaf ⟨135344,18,(.group 1 313 false)⟩)
(.leaf ⟨135362,18,(.group 1 314 false)⟩)))
(.branch 135416
(.branch 135398
(.leaf ⟨135380,18,(.group 1 315 false)⟩)
(.leaf ⟨135398,18,(.group 1 316 false)⟩))
(.branch 135434
(.leaf ⟨135416,18,(.group 1 317 false)⟩)
(.leaf ⟨135434,18,(.group 1 318 false)⟩))))
(.branch 135524
(.branch 135488
(.branch 135470
(.leaf ⟨135452,18,(.group 1 319 false)⟩)
(.leaf ⟨135470,18,(.group 1 320 false)⟩))
(.branch 135506
(.leaf ⟨135488,18,(.group 1 321 false)⟩)
(.leaf ⟨135506,18,(.group 1 322 false)⟩)))
(.branch 135560
(.branch 135542
(.leaf ⟨135524,18,(.group 1 323 false)⟩)
(.leaf ⟨135542,18,(.group 1 324 false)⟩))
(.branch 135578
(.leaf ⟨135560,18,(.group 1 325 false)⟩)
(.leaf ⟨135578,18,(.group 1 326 false)⟩)))))))

theorem tree135_checked : tree135.check 134444 135596 = true := by decide +kernel

def tree136 : Tree := (.branch 136172
(.branch 135884
(.branch 135740
(.branch 135668
(.branch 135632
(.branch 135614
(.leaf ⟨135596,18,(.group 1 327 false)⟩)
(.leaf ⟨135614,18,(.group 1 328 false)⟩))
(.branch 135650
(.leaf ⟨135632,18,(.group 1 329 false)⟩)
(.leaf ⟨135650,18,(.group 1 330 false)⟩)))
(.branch 135704
(.branch 135686
(.leaf ⟨135668,18,(.group 1 331 false)⟩)
(.leaf ⟨135686,18,(.group 1 332 false)⟩))
(.branch 135722
(.leaf ⟨135704,18,(.group 1 333 false)⟩)
(.leaf ⟨135722,18,(.group 1 334 false)⟩))))
(.branch 135812
(.branch 135776
(.branch 135758
(.leaf ⟨135740,18,(.group 1 335 false)⟩)
(.leaf ⟨135758,18,(.group 1 336 false)⟩))
(.branch 135794
(.leaf ⟨135776,18,(.group 1 337 false)⟩)
(.leaf ⟨135794,18,(.group 1 338 false)⟩)))
(.branch 135848
(.branch 135830
(.leaf ⟨135812,18,(.group 1 339 false)⟩)
(.leaf ⟨135830,18,(.group 1 340 false)⟩))
(.branch 135866
(.leaf ⟨135848,18,(.group 1 341 false)⟩)
(.leaf ⟨135866,18,(.group 1 342 false)⟩)))))
(.branch 136028
(.branch 135956
(.branch 135920
(.branch 135902
(.leaf ⟨135884,18,(.group 1 343 false)⟩)
(.leaf ⟨135902,18,(.group 1 344 false)⟩))
(.branch 135938
(.leaf ⟨135920,18,(.group 1 345 false)⟩)
(.leaf ⟨135938,18,(.group 1 346 false)⟩)))
(.branch 135992
(.branch 135974
(.leaf ⟨135956,18,(.group 1 347 false)⟩)
(.leaf ⟨135974,18,(.group 1 348 false)⟩))
(.branch 136010
(.leaf ⟨135992,18,(.group 1 349 false)⟩)
(.leaf ⟨136010,18,(.group 1 350 false)⟩))))
(.branch 136100
(.branch 136064
(.branch 136046
(.leaf ⟨136028,18,(.group 1 351 false)⟩)
(.leaf ⟨136046,18,(.group 1 352 false)⟩))
(.branch 136082
(.leaf ⟨136064,18,(.group 1 353 false)⟩)
(.leaf ⟨136082,18,(.group 1 354 false)⟩)))
(.branch 136136
(.branch 136118
(.leaf ⟨136100,18,(.group 1 355 false)⟩)
(.leaf ⟨136118,18,(.group 1 356 false)⟩))
(.branch 136154
(.leaf ⟨136136,18,(.group 1 357 false)⟩)
(.leaf ⟨136154,18,(.group 1 358 false)⟩))))))
(.branch 136460
(.branch 136316
(.branch 136244
(.branch 136208
(.branch 136190
(.leaf ⟨136172,18,(.group 1 359 false)⟩)
(.leaf ⟨136190,18,(.group 1 360 false)⟩))
(.branch 136226
(.leaf ⟨136208,18,(.group 1 361 false)⟩)
(.leaf ⟨136226,18,(.group 1 362 false)⟩)))
(.branch 136280
(.branch 136262
(.leaf ⟨136244,18,(.group 1 363 false)⟩)
(.leaf ⟨136262,18,(.group 2 286 false)⟩))
(.branch 136298
(.leaf ⟨136280,18,(.group 2 287 false)⟩)
(.leaf ⟨136298,18,(.group 2 288 false)⟩))))
(.branch 136388
(.branch 136352
(.branch 136334
(.leaf ⟨136316,18,(.group 2 289 false)⟩)
(.leaf ⟨136334,18,(.group 2 290 false)⟩))
(.branch 136370
(.leaf ⟨136352,18,(.group 2 291 false)⟩)
(.leaf ⟨136370,18,(.group 2 292 false)⟩)))
(.branch 136424
(.branch 136406
(.leaf ⟨136388,18,(.group 2 293 false)⟩)
(.leaf ⟨136406,18,(.group 2 294 false)⟩))
(.branch 136442
(.leaf ⟨136424,18,(.group 2 295 false)⟩)
(.leaf ⟨136442,18,(.group 2 296 false)⟩)))))
(.branch 136604
(.branch 136532
(.branch 136496
(.branch 136478
(.leaf ⟨136460,18,(.group 2 297 false)⟩)
(.leaf ⟨136478,18,(.group 2 298 false)⟩))
(.branch 136514
(.leaf ⟨136496,18,(.group 2 299 false)⟩)
(.leaf ⟨136514,18,(.group 2 300 false)⟩)))
(.branch 136568
(.branch 136550
(.leaf ⟨136532,18,(.group 2 301 false)⟩)
(.leaf ⟨136550,18,(.group 2 302 false)⟩))
(.branch 136586
(.leaf ⟨136568,18,(.group 2 303 false)⟩)
(.leaf ⟨136586,18,(.group 2 304 false)⟩))))
(.branch 136676
(.branch 136640
(.branch 136622
(.leaf ⟨136604,18,(.group 2 305 false)⟩)
(.leaf ⟨136622,18,(.group 2 306 false)⟩))
(.branch 136658
(.leaf ⟨136640,18,(.group 2 307 false)⟩)
(.leaf ⟨136658,18,(.group 2 308 false)⟩)))
(.branch 136712
(.branch 136694
(.leaf ⟨136676,18,(.group 2 309 false)⟩)
(.leaf ⟨136694,18,(.group 2 310 false)⟩))
(.branch 136730
(.leaf ⟨136712,18,(.group 2 311 false)⟩)
(.leaf ⟨136730,18,(.group 2 312 false)⟩)))))))

theorem tree136_checked : tree136.check 135596 136748 = true := by decide +kernel

def tree137 : Tree := (.branch 137324
(.branch 137036
(.branch 136892
(.branch 136820
(.branch 136784
(.branch 136766
(.leaf ⟨136748,18,(.group 2 313 false)⟩)
(.leaf ⟨136766,18,(.group 2 314 false)⟩))
(.branch 136802
(.leaf ⟨136784,18,(.group 2 315 false)⟩)
(.leaf ⟨136802,18,(.group 2 316 false)⟩)))
(.branch 136856
(.branch 136838
(.leaf ⟨136820,18,(.group 2 317 false)⟩)
(.leaf ⟨136838,18,(.group 2 318 false)⟩))
(.branch 136874
(.leaf ⟨136856,18,(.group 2 319 false)⟩)
(.leaf ⟨136874,18,(.group 2 320 false)⟩))))
(.branch 136964
(.branch 136928
(.branch 136910
(.leaf ⟨136892,18,(.group 2 321 false)⟩)
(.leaf ⟨136910,18,(.group 2 322 false)⟩))
(.branch 136946
(.leaf ⟨136928,18,(.group 2 323 false)⟩)
(.leaf ⟨136946,18,(.group 2 324 false)⟩)))
(.branch 137000
(.branch 136982
(.leaf ⟨136964,18,(.group 2 325 false)⟩)
(.leaf ⟨136982,18,(.group 2 326 false)⟩))
(.branch 137018
(.leaf ⟨137000,18,(.group 2 327 false)⟩)
(.leaf ⟨137018,18,(.group 2 328 false)⟩)))))
(.branch 137180
(.branch 137108
(.branch 137072
(.branch 137054
(.leaf ⟨137036,18,(.group 2 329 false)⟩)
(.leaf ⟨137054,18,(.group 2 330 false)⟩))
(.branch 137090
(.leaf ⟨137072,18,(.group 2 331 false)⟩)
(.leaf ⟨137090,18,(.group 2 332 false)⟩)))
(.branch 137144
(.branch 137126
(.leaf ⟨137108,18,(.group 2 333 false)⟩)
(.leaf ⟨137126,18,(.group 2 334 false)⟩))
(.branch 137162
(.leaf ⟨137144,18,(.group 2 335 false)⟩)
(.leaf ⟨137162,18,(.group 2 336 false)⟩))))
(.branch 137252
(.branch 137216
(.branch 137198
(.leaf ⟨137180,18,(.group 2 337 false)⟩)
(.leaf ⟨137198,18,(.group 2 338 false)⟩))
(.branch 137234
(.leaf ⟨137216,18,(.group 2 339 false)⟩)
(.leaf ⟨137234,18,(.group 2 340 false)⟩)))
(.branch 137288
(.branch 137270
(.leaf ⟨137252,18,(.group 2 341 false)⟩)
(.leaf ⟨137270,18,(.group 2 342 false)⟩))
(.branch 137306
(.leaf ⟨137288,18,(.group 2 343 false)⟩)
(.leaf ⟨137306,18,(.group 2 344 false)⟩))))))
(.branch 137612
(.branch 137468
(.branch 137396
(.branch 137360
(.branch 137342
(.leaf ⟨137324,18,(.group 2 345 false)⟩)
(.leaf ⟨137342,18,(.group 2 346 false)⟩))
(.branch 137378
(.leaf ⟨137360,18,(.group 2 347 false)⟩)
(.leaf ⟨137378,18,(.group 2 348 false)⟩)))
(.branch 137432
(.branch 137414
(.leaf ⟨137396,18,(.group 2 349 false)⟩)
(.leaf ⟨137414,18,(.group 2 350 false)⟩))
(.branch 137450
(.leaf ⟨137432,18,(.group 2 351 false)⟩)
(.leaf ⟨137450,18,(.group 2 352 false)⟩))))
(.branch 137540
(.branch 137504
(.branch 137486
(.leaf ⟨137468,18,(.group 2 353 false)⟩)
(.leaf ⟨137486,18,(.group 2 354 false)⟩))
(.branch 137522
(.leaf ⟨137504,18,(.group 2 355 false)⟩)
(.leaf ⟨137522,18,(.group 2 356 false)⟩)))
(.branch 137576
(.branch 137558
(.leaf ⟨137540,18,(.group 2 357 false)⟩)
(.leaf ⟨137558,18,(.group 2 358 false)⟩))
(.branch 137594
(.leaf ⟨137576,18,(.group 2 359 false)⟩)
(.leaf ⟨137594,18,(.group 2 360 false)⟩)))))
(.branch 137756
(.branch 137684
(.branch 137648
(.branch 137630
(.leaf ⟨137612,18,(.group 2 361 false)⟩)
(.leaf ⟨137630,18,(.group 2 362 false)⟩))
(.branch 137666
(.leaf ⟨137648,18,(.group 2 363 false)⟩)
(.leaf ⟨137666,18,(.group 3 286 false)⟩)))
(.branch 137720
(.branch 137702
(.leaf ⟨137684,18,(.group 3 287 false)⟩)
(.leaf ⟨137702,18,(.group 3 288 false)⟩))
(.branch 137738
(.leaf ⟨137720,18,(.group 3 289 false)⟩)
(.leaf ⟨137738,18,(.group 3 290 false)⟩))))
(.branch 137828
(.branch 137792
(.branch 137774
(.leaf ⟨137756,18,(.group 3 291 false)⟩)
(.leaf ⟨137774,18,(.group 3 292 false)⟩))
(.branch 137810
(.leaf ⟨137792,18,(.group 3 293 false)⟩)
(.leaf ⟨137810,18,(.group 3 294 false)⟩)))
(.branch 137864
(.branch 137846
(.leaf ⟨137828,18,(.group 3 295 false)⟩)
(.leaf ⟨137846,18,(.group 3 296 false)⟩))
(.branch 137882
(.leaf ⟨137864,18,(.group 3 297 false)⟩)
(.leaf ⟨137882,18,(.group 3 298 false)⟩)))))))

theorem tree137_checked : tree137.check 136748 137900 = true := by decide +kernel

def tree138 : Tree := (.branch 138476
(.branch 138188
(.branch 138044
(.branch 137972
(.branch 137936
(.branch 137918
(.leaf ⟨137900,18,(.group 3 299 false)⟩)
(.leaf ⟨137918,18,(.group 3 300 false)⟩))
(.branch 137954
(.leaf ⟨137936,18,(.group 3 301 false)⟩)
(.leaf ⟨137954,18,(.group 3 302 false)⟩)))
(.branch 138008
(.branch 137990
(.leaf ⟨137972,18,(.group 3 303 false)⟩)
(.leaf ⟨137990,18,(.group 3 304 false)⟩))
(.branch 138026
(.leaf ⟨138008,18,(.group 3 305 false)⟩)
(.leaf ⟨138026,18,(.group 3 306 false)⟩))))
(.branch 138116
(.branch 138080
(.branch 138062
(.leaf ⟨138044,18,(.group 3 307 false)⟩)
(.leaf ⟨138062,18,(.group 3 308 false)⟩))
(.branch 138098
(.leaf ⟨138080,18,(.group 3 309 false)⟩)
(.leaf ⟨138098,18,(.group 3 310 false)⟩)))
(.branch 138152
(.branch 138134
(.leaf ⟨138116,18,(.group 3 311 false)⟩)
(.leaf ⟨138134,18,(.group 3 312 false)⟩))
(.branch 138170
(.leaf ⟨138152,18,(.group 3 313 false)⟩)
(.leaf ⟨138170,18,(.group 3 314 false)⟩)))))
(.branch 138332
(.branch 138260
(.branch 138224
(.branch 138206
(.leaf ⟨138188,18,(.group 3 315 false)⟩)
(.leaf ⟨138206,18,(.group 3 316 false)⟩))
(.branch 138242
(.leaf ⟨138224,18,(.group 3 317 false)⟩)
(.leaf ⟨138242,18,(.group 3 318 false)⟩)))
(.branch 138296
(.branch 138278
(.leaf ⟨138260,18,(.group 3 319 false)⟩)
(.leaf ⟨138278,18,(.group 3 320 false)⟩))
(.branch 138314
(.leaf ⟨138296,18,(.group 3 321 false)⟩)
(.leaf ⟨138314,18,(.group 3 322 false)⟩))))
(.branch 138404
(.branch 138368
(.branch 138350
(.leaf ⟨138332,18,(.group 3 323 false)⟩)
(.leaf ⟨138350,18,(.group 3 324 false)⟩))
(.branch 138386
(.leaf ⟨138368,18,(.group 3 325 false)⟩)
(.leaf ⟨138386,18,(.group 3 326 false)⟩)))
(.branch 138440
(.branch 138422
(.leaf ⟨138404,18,(.group 3 327 false)⟩)
(.leaf ⟨138422,18,(.group 3 328 false)⟩))
(.branch 138458
(.leaf ⟨138440,18,(.group 3 329 false)⟩)
(.leaf ⟨138458,18,(.group 3 330 false)⟩))))))
(.branch 138764
(.branch 138620
(.branch 138548
(.branch 138512
(.branch 138494
(.leaf ⟨138476,18,(.group 3 331 false)⟩)
(.leaf ⟨138494,18,(.group 3 332 false)⟩))
(.branch 138530
(.leaf ⟨138512,18,(.group 3 333 false)⟩)
(.leaf ⟨138530,18,(.group 3 334 false)⟩)))
(.branch 138584
(.branch 138566
(.leaf ⟨138548,18,(.group 3 335 false)⟩)
(.leaf ⟨138566,18,(.group 3 336 false)⟩))
(.branch 138602
(.leaf ⟨138584,18,(.group 3 337 false)⟩)
(.leaf ⟨138602,18,(.group 3 338 false)⟩))))
(.branch 138692
(.branch 138656
(.branch 138638
(.leaf ⟨138620,18,(.group 3 339 false)⟩)
(.leaf ⟨138638,18,(.group 3 340 false)⟩))
(.branch 138674
(.leaf ⟨138656,18,(.group 3 341 false)⟩)
(.leaf ⟨138674,18,(.group 3 342 false)⟩)))
(.branch 138728
(.branch 138710
(.leaf ⟨138692,18,(.group 3 343 false)⟩)
(.leaf ⟨138710,18,(.group 3 344 false)⟩))
(.branch 138746
(.leaf ⟨138728,18,(.group 3 345 false)⟩)
(.leaf ⟨138746,18,(.group 3 346 false)⟩)))))
(.branch 138908
(.branch 138836
(.branch 138800
(.branch 138782
(.leaf ⟨138764,18,(.group 3 347 false)⟩)
(.leaf ⟨138782,18,(.group 3 348 false)⟩))
(.branch 138818
(.leaf ⟨138800,18,(.group 3 349 false)⟩)
(.leaf ⟨138818,18,(.group 3 350 false)⟩)))
(.branch 138872
(.branch 138854
(.leaf ⟨138836,18,(.group 3 351 false)⟩)
(.leaf ⟨138854,18,(.group 3 352 false)⟩))
(.branch 138890
(.leaf ⟨138872,18,(.group 3 353 false)⟩)
(.leaf ⟨138890,18,(.group 3 354 false)⟩))))
(.branch 138980
(.branch 138944
(.branch 138926
(.leaf ⟨138908,18,(.group 3 355 false)⟩)
(.leaf ⟨138926,18,(.group 3 356 false)⟩))
(.branch 138962
(.leaf ⟨138944,18,(.group 3 357 false)⟩)
(.leaf ⟨138962,18,(.group 3 358 false)⟩)))
(.branch 139016
(.branch 138998
(.leaf ⟨138980,18,(.group 3 359 false)⟩)
(.leaf ⟨138998,18,(.group 3 360 false)⟩))
(.branch 139034
(.leaf ⟨139016,18,(.group 3 361 false)⟩)
(.leaf ⟨139034,18,(.group 3 362 false)⟩)))))))

theorem tree138_checked : tree138.check 137900 139052 = true := by decide +kernel

def tree139 : Tree := (.branch 139628
(.branch 139340
(.branch 139196
(.branch 139124
(.branch 139088
(.branch 139070
(.leaf ⟨139052,18,(.group 3 363 false)⟩)
(.leaf ⟨139070,18,(.group 4 286 false)⟩))
(.branch 139106
(.leaf ⟨139088,18,(.group 4 287 false)⟩)
(.leaf ⟨139106,18,(.group 4 288 false)⟩)))
(.branch 139160
(.branch 139142
(.leaf ⟨139124,18,(.group 4 289 false)⟩)
(.leaf ⟨139142,18,(.group 4 290 false)⟩))
(.branch 139178
(.leaf ⟨139160,18,(.group 4 291 false)⟩)
(.leaf ⟨139178,18,(.group 4 292 false)⟩))))
(.branch 139268
(.branch 139232
(.branch 139214
(.leaf ⟨139196,18,(.group 4 293 false)⟩)
(.leaf ⟨139214,18,(.group 4 294 false)⟩))
(.branch 139250
(.leaf ⟨139232,18,(.group 4 295 false)⟩)
(.leaf ⟨139250,18,(.group 4 296 false)⟩)))
(.branch 139304
(.branch 139286
(.leaf ⟨139268,18,(.group 4 297 false)⟩)
(.leaf ⟨139286,18,(.group 4 298 false)⟩))
(.branch 139322
(.leaf ⟨139304,18,(.group 4 299 false)⟩)
(.leaf ⟨139322,18,(.group 4 300 false)⟩)))))
(.branch 139484
(.branch 139412
(.branch 139376
(.branch 139358
(.leaf ⟨139340,18,(.group 4 301 false)⟩)
(.leaf ⟨139358,18,(.group 4 302 false)⟩))
(.branch 139394
(.leaf ⟨139376,18,(.group 4 303 false)⟩)
(.leaf ⟨139394,18,(.group 4 304 false)⟩)))
(.branch 139448
(.branch 139430
(.leaf ⟨139412,18,(.group 4 305 false)⟩)
(.leaf ⟨139430,18,(.group 4 306 false)⟩))
(.branch 139466
(.leaf ⟨139448,18,(.group 4 307 false)⟩)
(.leaf ⟨139466,18,(.group 4 308 false)⟩))))
(.branch 139556
(.branch 139520
(.branch 139502
(.leaf ⟨139484,18,(.group 4 309 false)⟩)
(.leaf ⟨139502,18,(.group 4 310 false)⟩))
(.branch 139538
(.leaf ⟨139520,18,(.group 4 311 false)⟩)
(.leaf ⟨139538,18,(.group 4 312 false)⟩)))
(.branch 139592
(.branch 139574
(.leaf ⟨139556,18,(.group 4 313 false)⟩)
(.leaf ⟨139574,18,(.group 4 314 false)⟩))
(.branch 139610
(.leaf ⟨139592,18,(.group 4 315 false)⟩)
(.leaf ⟨139610,18,(.group 4 316 false)⟩))))))
(.branch 139916
(.branch 139772
(.branch 139700
(.branch 139664
(.branch 139646
(.leaf ⟨139628,18,(.group 4 317 false)⟩)
(.leaf ⟨139646,18,(.group 4 318 false)⟩))
(.branch 139682
(.leaf ⟨139664,18,(.group 4 319 false)⟩)
(.leaf ⟨139682,18,(.group 4 320 false)⟩)))
(.branch 139736
(.branch 139718
(.leaf ⟨139700,18,(.group 4 321 false)⟩)
(.leaf ⟨139718,18,(.group 4 322 false)⟩))
(.branch 139754
(.leaf ⟨139736,18,(.group 4 323 false)⟩)
(.leaf ⟨139754,18,(.group 4 324 false)⟩))))
(.branch 139844
(.branch 139808
(.branch 139790
(.leaf ⟨139772,18,(.group 4 325 false)⟩)
(.leaf ⟨139790,18,(.group 4 326 false)⟩))
(.branch 139826
(.leaf ⟨139808,18,(.group 4 327 false)⟩)
(.leaf ⟨139826,18,(.group 4 328 false)⟩)))
(.branch 139880
(.branch 139862
(.leaf ⟨139844,18,(.group 4 329 false)⟩)
(.leaf ⟨139862,18,(.group 4 330 false)⟩))
(.branch 139898
(.leaf ⟨139880,18,(.group 4 331 false)⟩)
(.leaf ⟨139898,18,(.group 4 332 false)⟩)))))
(.branch 140060
(.branch 139988
(.branch 139952
(.branch 139934
(.leaf ⟨139916,18,(.group 4 333 false)⟩)
(.leaf ⟨139934,18,(.group 4 334 false)⟩))
(.branch 139970
(.leaf ⟨139952,18,(.group 4 335 false)⟩)
(.leaf ⟨139970,18,(.group 4 336 false)⟩)))
(.branch 140024
(.branch 140006
(.leaf ⟨139988,18,(.group 4 337 false)⟩)
(.leaf ⟨140006,18,(.group 4 338 false)⟩))
(.branch 140042
(.leaf ⟨140024,18,(.group 4 339 false)⟩)
(.leaf ⟨140042,18,(.group 4 340 false)⟩))))
(.branch 140132
(.branch 140096
(.branch 140078
(.leaf ⟨140060,18,(.group 4 341 false)⟩)
(.leaf ⟨140078,18,(.group 4 342 false)⟩))
(.branch 140114
(.leaf ⟨140096,18,(.group 4 343 false)⟩)
(.leaf ⟨140114,18,(.group 4 344 false)⟩)))
(.branch 140168
(.branch 140150
(.leaf ⟨140132,18,(.group 4 345 false)⟩)
(.leaf ⟨140150,18,(.group 4 346 false)⟩))
(.branch 140186
(.leaf ⟨140168,18,(.group 4 347 false)⟩)
(.leaf ⟨140186,18,(.group 4 348 false)⟩)))))))

theorem tree139_checked : tree139.check 139052 140204 = true := by decide +kernel

def tree140 : Tree := (.branch 140780
(.branch 140492
(.branch 140348
(.branch 140276
(.branch 140240
(.branch 140222
(.leaf ⟨140204,18,(.group 4 349 false)⟩)
(.leaf ⟨140222,18,(.group 4 350 false)⟩))
(.branch 140258
(.leaf ⟨140240,18,(.group 4 351 false)⟩)
(.leaf ⟨140258,18,(.group 4 352 false)⟩)))
(.branch 140312
(.branch 140294
(.leaf ⟨140276,18,(.group 4 353 false)⟩)
(.leaf ⟨140294,18,(.group 4 354 false)⟩))
(.branch 140330
(.leaf ⟨140312,18,(.group 4 355 false)⟩)
(.leaf ⟨140330,18,(.group 4 356 false)⟩))))
(.branch 140420
(.branch 140384
(.branch 140366
(.leaf ⟨140348,18,(.group 4 357 false)⟩)
(.leaf ⟨140366,18,(.group 4 358 false)⟩))
(.branch 140402
(.leaf ⟨140384,18,(.group 4 359 false)⟩)
(.leaf ⟨140402,18,(.group 4 360 false)⟩)))
(.branch 140456
(.branch 140438
(.leaf ⟨140420,18,(.group 4 361 false)⟩)
(.leaf ⟨140438,18,(.group 4 362 false)⟩))
(.branch 140474
(.leaf ⟨140456,18,(.group 4 363 false)⟩)
(.leaf ⟨140474,18,(.group 5 1877 false)⟩)))))
(.branch 140636
(.branch 140564
(.branch 140528
(.branch 140510
(.leaf ⟨140492,18,(.group 5 1878 false)⟩)
(.leaf ⟨140510,18,(.group 5 1879 false)⟩))
(.branch 140546
(.leaf ⟨140528,18,(.group 5 1880 false)⟩)
(.leaf ⟨140546,18,(.group 5 1881 false)⟩)))
(.branch 140600
(.branch 140582
(.leaf ⟨140564,18,(.group 5 1882 false)⟩)
(.leaf ⟨140582,18,(.group 5 1883 false)⟩))
(.branch 140618
(.leaf ⟨140600,18,(.group 5 1884 false)⟩)
(.leaf ⟨140618,18,(.group 5 1885 false)⟩))))
(.branch 140708
(.branch 140672
(.branch 140654
(.leaf ⟨140636,18,(.group 5 1886 false)⟩)
(.leaf ⟨140654,18,(.group 5 1887 false)⟩))
(.branch 140690
(.leaf ⟨140672,18,(.group 5 1888 false)⟩)
(.leaf ⟨140690,18,(.group 5 1889 false)⟩)))
(.branch 140744
(.branch 140726
(.leaf ⟨140708,18,(.group 5 1890 false)⟩)
(.leaf ⟨140726,18,(.group 5 1891 false)⟩))
(.branch 140762
(.leaf ⟨140744,18,(.group 5 1892 false)⟩)
(.leaf ⟨140762,18,(.group 5 1893 false)⟩))))))
(.branch 141068
(.branch 140924
(.branch 140852
(.branch 140816
(.branch 140798
(.leaf ⟨140780,18,(.group 5 1894 false)⟩)
(.leaf ⟨140798,18,(.group 5 1895 false)⟩))
(.branch 140834
(.leaf ⟨140816,18,(.group 5 1896 false)⟩)
(.leaf ⟨140834,18,(.group 5 1897 false)⟩)))
(.branch 140888
(.branch 140870
(.leaf ⟨140852,18,(.group 5 1898 false)⟩)
(.leaf ⟨140870,18,(.group 5 1899 false)⟩))
(.branch 140906
(.leaf ⟨140888,18,(.group 5 1900 false)⟩)
(.leaf ⟨140906,18,(.group 5 1901 false)⟩))))
(.branch 140996
(.branch 140960
(.branch 140942
(.leaf ⟨140924,18,(.group 5 1902 false)⟩)
(.leaf ⟨140942,18,(.group 5 1903 false)⟩))
(.branch 140978
(.leaf ⟨140960,18,(.group 5 1904 false)⟩)
(.leaf ⟨140978,18,(.group 5 1905 false)⟩)))
(.branch 141032
(.branch 141014
(.leaf ⟨140996,18,(.group 5 1906 false)⟩)
(.leaf ⟨141014,18,(.group 5 1907 false)⟩))
(.branch 141050
(.leaf ⟨141032,18,(.group 5 1908 false)⟩)
(.leaf ⟨141050,18,(.group 5 1909 false)⟩)))))
(.branch 141212
(.branch 141140
(.branch 141104
(.branch 141086
(.leaf ⟨141068,18,(.group 5 1910 false)⟩)
(.leaf ⟨141086,18,(.group 5 1911 false)⟩))
(.branch 141122
(.leaf ⟨141104,18,(.group 5 1912 false)⟩)
(.leaf ⟨141122,18,(.group 5 1913 false)⟩)))
(.branch 141176
(.branch 141158
(.leaf ⟨141140,18,(.group 5 1914 false)⟩)
(.leaf ⟨141158,18,(.group 5 1915 false)⟩))
(.branch 141194
(.leaf ⟨141176,18,(.group 5 1916 false)⟩)
(.leaf ⟨141194,18,(.group 5 1917 false)⟩))))
(.branch 141284
(.branch 141248
(.branch 141230
(.leaf ⟨141212,18,(.group 5 1918 false)⟩)
(.leaf ⟨141230,18,(.group 5 1919 false)⟩))
(.branch 141266
(.leaf ⟨141248,18,(.group 5 1920 false)⟩)
(.leaf ⟨141266,18,(.group 5 1921 false)⟩)))
(.branch 141320
(.branch 141302
(.leaf ⟨141284,18,(.group 5 1922 false)⟩)
(.leaf ⟨141302,18,(.group 5 1923 false)⟩))
(.branch 141338
(.leaf ⟨141320,18,(.group 5 1924 false)⟩)
(.leaf ⟨141338,18,(.group 5 1925 false)⟩)))))))

theorem tree140_checked : tree140.check 140204 141356 = true := by decide +kernel

def tree141 : Tree := (.branch 141932
(.branch 141644
(.branch 141500
(.branch 141428
(.branch 141392
(.branch 141374
(.leaf ⟨141356,18,(.group 5 1926 false)⟩)
(.leaf ⟨141374,18,(.group 5 1927 false)⟩))
(.branch 141410
(.leaf ⟨141392,18,(.group 5 1928 false)⟩)
(.leaf ⟨141410,18,(.group 5 1929 false)⟩)))
(.branch 141464
(.branch 141446
(.leaf ⟨141428,18,(.group 5 1930 false)⟩)
(.leaf ⟨141446,18,(.group 5 1931 false)⟩))
(.branch 141482
(.leaf ⟨141464,18,(.group 5 1932 false)⟩)
(.leaf ⟨141482,18,(.group 5 1933 false)⟩))))
(.branch 141572
(.branch 141536
(.branch 141518
(.leaf ⟨141500,18,(.group 5 1934 false)⟩)
(.leaf ⟨141518,18,(.group 5 1935 false)⟩))
(.branch 141554
(.leaf ⟨141536,18,(.group 5 1936 false)⟩)
(.leaf ⟨141554,18,(.group 5 1937 false)⟩)))
(.branch 141608
(.branch 141590
(.leaf ⟨141572,18,(.group 5 1938 false)⟩)
(.leaf ⟨141590,18,(.group 5 1939 false)⟩))
(.branch 141626
(.leaf ⟨141608,18,(.group 5 1940 false)⟩)
(.leaf ⟨141626,18,(.group 5 1941 false)⟩)))))
(.branch 141788
(.branch 141716
(.branch 141680
(.branch 141662
(.leaf ⟨141644,18,(.group 5 1942 false)⟩)
(.leaf ⟨141662,18,(.group 5 1943 false)⟩))
(.branch 141698
(.leaf ⟨141680,18,(.group 5 1944 false)⟩)
(.leaf ⟨141698,18,(.group 5 1945 false)⟩)))
(.branch 141752
(.branch 141734
(.leaf ⟨141716,18,(.group 5 1946 false)⟩)
(.leaf ⟨141734,18,(.group 5 1947 false)⟩))
(.branch 141770
(.leaf ⟨141752,18,(.group 5 1948 false)⟩)
(.leaf ⟨141770,18,(.group 5 1949 false)⟩))))
(.branch 141860
(.branch 141824
(.branch 141806
(.leaf ⟨141788,18,(.group 5 1950 false)⟩)
(.leaf ⟨141806,18,(.group 5 1951 false)⟩))
(.branch 141842
(.leaf ⟨141824,18,(.group 5 1952 false)⟩)
(.leaf ⟨141842,18,(.group 5 1953 false)⟩)))
(.branch 141896
(.branch 141878
(.leaf ⟨141860,18,(.group 5 1954 false)⟩)
(.leaf ⟨141878,18,(.group 5 1955 false)⟩))
(.branch 141914
(.leaf ⟨141896,18,(.group 5 1956 false)⟩)
(.leaf ⟨141914,18,(.group 5 1957 false)⟩))))))
(.branch 142220
(.branch 142076
(.branch 142004
(.branch 141968
(.branch 141950
(.leaf ⟨141932,18,(.group 5 1958 false)⟩)
(.leaf ⟨141950,18,(.group 5 1959 false)⟩))
(.branch 141986
(.leaf ⟨141968,18,(.group 5 1960 false)⟩)
(.leaf ⟨141986,18,(.group 5 1961 false)⟩)))
(.branch 142040
(.branch 142022
(.leaf ⟨142004,18,(.group 5 1962 false)⟩)
(.leaf ⟨142022,18,(.group 5 1963 false)⟩))
(.branch 142058
(.leaf ⟨142040,18,(.group 5 1964 false)⟩)
(.leaf ⟨142058,18,(.group 5 1965 false)⟩))))
(.branch 142148
(.branch 142112
(.branch 142094
(.leaf ⟨142076,18,(.group 5 1966 false)⟩)
(.leaf ⟨142094,18,(.group 5 1967 false)⟩))
(.branch 142130
(.leaf ⟨142112,18,(.group 5 1968 false)⟩)
(.leaf ⟨142130,18,(.group 5 1969 false)⟩)))
(.branch 142184
(.branch 142166
(.leaf ⟨142148,18,(.group 5 1970 false)⟩)
(.leaf ⟨142166,18,(.group 5 1971 false)⟩))
(.branch 142202
(.leaf ⟨142184,18,(.group 5 1972 false)⟩)
(.leaf ⟨142202,18,(.group 5 1973 false)⟩)))))
(.branch 142364
(.branch 142292
(.branch 142256
(.branch 142238
(.leaf ⟨142220,18,(.group 5 1974 false)⟩)
(.leaf ⟨142238,18,(.group 5 1975 false)⟩))
(.branch 142274
(.leaf ⟨142256,18,(.group 5 1976 false)⟩)
(.leaf ⟨142274,18,(.group 5 1977 false)⟩)))
(.branch 142328
(.branch 142310
(.leaf ⟨142292,18,(.group 5 1978 false)⟩)
(.leaf ⟨142310,18,(.group 5 1979 false)⟩))
(.branch 142346
(.leaf ⟨142328,18,(.group 5 1980 false)⟩)
(.leaf ⟨142346,18,(.group 5 1981 false)⟩))))
(.branch 142436
(.branch 142400
(.branch 142382
(.leaf ⟨142364,18,(.group 5 1982 false)⟩)
(.leaf ⟨142382,18,(.group 5 1983 false)⟩))
(.branch 142418
(.leaf ⟨142400,18,(.group 5 1984 false)⟩)
(.leaf ⟨142418,18,(.group 5 1985 false)⟩)))
(.branch 142472
(.branch 142454
(.leaf ⟨142436,18,(.group 5 1986 false)⟩)
(.leaf ⟨142454,18,(.group 5 1987 false)⟩))
(.branch 142490
(.leaf ⟨142472,18,(.group 5 1988 false)⟩)
(.leaf ⟨142490,18,(.group 5 1989 false)⟩)))))))

theorem tree141_checked : tree141.check 141356 142508 = true := by decide +kernel

def tree142 : Tree := (.branch 143084
(.branch 142796
(.branch 142652
(.branch 142580
(.branch 142544
(.branch 142526
(.leaf ⟨142508,18,(.group 5 1990 false)⟩)
(.leaf ⟨142526,18,(.group 5 1991 false)⟩))
(.branch 142562
(.leaf ⟨142544,18,(.group 5 1992 false)⟩)
(.leaf ⟨142562,18,(.group 5 1993 false)⟩)))
(.branch 142616
(.branch 142598
(.leaf ⟨142580,18,(.group 5 1994 false)⟩)
(.leaf ⟨142598,18,(.group 5 1995 false)⟩))
(.branch 142634
(.leaf ⟨142616,18,(.group 5 1996 false)⟩)
(.leaf ⟨142634,18,(.group 5 1997 false)⟩))))
(.branch 142724
(.branch 142688
(.branch 142670
(.leaf ⟨142652,18,(.group 5 1998 false)⟩)
(.leaf ⟨142670,18,(.group 5 1999 false)⟩))
(.branch 142706
(.leaf ⟨142688,18,(.group 5 2000 false)⟩)
(.leaf ⟨142706,18,(.group 5 2001 false)⟩)))
(.branch 142760
(.branch 142742
(.leaf ⟨142724,18,(.group 5 2002 false)⟩)
(.leaf ⟨142742,18,(.group 5 2003 false)⟩))
(.branch 142778
(.leaf ⟨142760,18,(.group 5 2004 false)⟩)
(.leaf ⟨142778,18,(.group 5 2005 false)⟩)))))
(.branch 142940
(.branch 142868
(.branch 142832
(.branch 142814
(.leaf ⟨142796,18,(.group 5 2006 false)⟩)
(.leaf ⟨142814,18,(.group 5 2007 false)⟩))
(.branch 142850
(.leaf ⟨142832,18,(.group 5 2008 false)⟩)
(.leaf ⟨142850,18,(.group 5 2009 false)⟩)))
(.branch 142904
(.branch 142886
(.leaf ⟨142868,18,(.group 5 2010 false)⟩)
(.leaf ⟨142886,18,(.group 5 2011 false)⟩))
(.branch 142922
(.leaf ⟨142904,18,(.group 5 2012 false)⟩)
(.leaf ⟨142922,18,(.group 5 2013 false)⟩))))
(.branch 143012
(.branch 142976
(.branch 142958
(.leaf ⟨142940,18,(.group 5 2014 false)⟩)
(.leaf ⟨142958,18,(.group 5 2015 false)⟩))
(.branch 142994
(.leaf ⟨142976,18,(.group 5 2016 false)⟩)
(.leaf ⟨142994,18,(.group 5 2017 false)⟩)))
(.branch 143048
(.branch 143030
(.leaf ⟨143012,18,(.group 5 2018 false)⟩)
(.leaf ⟨143030,18,(.group 5 2019 false)⟩))
(.branch 143066
(.leaf ⟨143048,18,(.group 5 2020 false)⟩)
(.leaf ⟨143066,18,(.group 5 2021 false)⟩))))))
(.branch 143372
(.branch 143228
(.branch 143156
(.branch 143120
(.branch 143102
(.leaf ⟨143084,18,(.group 5 2022 false)⟩)
(.leaf ⟨143102,18,(.group 5 2023 false)⟩))
(.branch 143138
(.leaf ⟨143120,18,(.group 5 2024 false)⟩)
(.leaf ⟨143138,18,(.group 5 2025 false)⟩)))
(.branch 143192
(.branch 143174
(.leaf ⟨143156,18,(.group 5 2026 false)⟩)
(.leaf ⟨143174,18,(.group 5 2027 false)⟩))
(.branch 143210
(.leaf ⟨143192,18,(.group 5 2028 false)⟩)
(.leaf ⟨143210,18,(.group 5 2029 false)⟩))))
(.branch 143300
(.branch 143264
(.branch 143246
(.leaf ⟨143228,18,(.group 5 2030 false)⟩)
(.leaf ⟨143246,18,(.group 5 2031 false)⟩))
(.branch 143282
(.leaf ⟨143264,18,(.group 5 2032 false)⟩)
(.leaf ⟨143282,18,(.group 5 2033 false)⟩)))
(.branch 143336
(.branch 143318
(.leaf ⟨143300,18,(.group 5 2034 false)⟩)
(.leaf ⟨143318,18,(.group 5 2035 false)⟩))
(.branch 143354
(.leaf ⟨143336,18,(.group 5 2036 false)⟩)
(.leaf ⟨143354,18,(.group 5 2037 false)⟩)))))
(.branch 143516
(.branch 143444
(.branch 143408
(.branch 143390
(.leaf ⟨143372,18,(.group 5 2038 false)⟩)
(.leaf ⟨143390,18,(.group 5 2039 false)⟩))
(.branch 143426
(.leaf ⟨143408,18,(.group 5 2040 false)⟩)
(.leaf ⟨143426,18,(.group 5 2041 false)⟩)))
(.branch 143480
(.branch 143462
(.leaf ⟨143444,18,(.group 5 2042 false)⟩)
(.leaf ⟨143462,18,(.group 5 2043 false)⟩))
(.branch 143498
(.leaf ⟨143480,18,(.group 5 2044 false)⟩)
(.leaf ⟨143498,18,(.group 5 2045 false)⟩))))
(.branch 143588
(.branch 143552
(.branch 143534
(.leaf ⟨143516,18,(.group 5 2046 false)⟩)
(.leaf ⟨143534,18,(.group 5 2047 false)⟩))
(.branch 143570
(.leaf ⟨143552,18,(.group 5 2048 false)⟩)
(.leaf ⟨143570,18,(.group 5 2049 false)⟩)))
(.branch 143624
(.branch 143606
(.leaf ⟨143588,18,(.group 5 2050 false)⟩)
(.leaf ⟨143606,18,(.group 5 2051 false)⟩))
(.branch 143642
(.leaf ⟨143624,18,(.group 5 2052 false)⟩)
(.leaf ⟨143642,18,(.group 5 2053 false)⟩)))))))

theorem tree142_checked : tree142.check 142508 143660 = true := by decide +kernel

def tree143 : Tree := (.branch 144236
(.branch 143948
(.branch 143804
(.branch 143732
(.branch 143696
(.branch 143678
(.leaf ⟨143660,18,(.group 5 2054 false)⟩)
(.leaf ⟨143678,18,(.group 5 2055 false)⟩))
(.branch 143714
(.leaf ⟨143696,18,(.group 5 2056 false)⟩)
(.leaf ⟨143714,18,(.group 5 2057 false)⟩)))
(.branch 143768
(.branch 143750
(.leaf ⟨143732,18,(.group 5 2058 false)⟩)
(.leaf ⟨143750,18,(.group 5 2059 false)⟩))
(.branch 143786
(.leaf ⟨143768,18,(.group 5 2060 false)⟩)
(.leaf ⟨143786,18,(.group 5 2061 false)⟩))))
(.branch 143876
(.branch 143840
(.branch 143822
(.leaf ⟨143804,18,(.group 5 2062 false)⟩)
(.leaf ⟨143822,18,(.group 5 2063 false)⟩))
(.branch 143858
(.leaf ⟨143840,18,(.group 5 2064 false)⟩)
(.leaf ⟨143858,18,(.group 5 2065 false)⟩)))
(.branch 143912
(.branch 143894
(.leaf ⟨143876,18,(.group 5 2066 false)⟩)
(.leaf ⟨143894,18,(.group 5 2067 false)⟩))
(.branch 143930
(.leaf ⟨143912,18,(.group 5 2068 false)⟩)
(.leaf ⟨143930,18,(.group 5 2069 false)⟩)))))
(.branch 144092
(.branch 144020
(.branch 143984
(.branch 143966
(.leaf ⟨143948,18,(.group 5 2070 false)⟩)
(.leaf ⟨143966,18,(.group 5 2071 false)⟩))
(.branch 144002
(.leaf ⟨143984,18,(.group 5 2072 false)⟩)
(.leaf ⟨144002,18,(.group 5 2073 false)⟩)))
(.branch 144056
(.branch 144038
(.leaf ⟨144020,18,(.group 5 2074 false)⟩)
(.leaf ⟨144038,18,(.group 5 2075 false)⟩))
(.branch 144074
(.leaf ⟨144056,18,(.group 5 2076 false)⟩)
(.leaf ⟨144074,18,(.group 5 2077 false)⟩))))
(.branch 144164
(.branch 144128
(.branch 144110
(.leaf ⟨144092,18,(.group 5 2078 false)⟩)
(.leaf ⟨144110,18,(.group 5 2079 false)⟩))
(.branch 144146
(.leaf ⟨144128,18,(.group 5 2080 false)⟩)
(.leaf ⟨144146,18,(.group 5 2081 false)⟩)))
(.branch 144200
(.branch 144182
(.leaf ⟨144164,18,(.group 5 2082 false)⟩)
(.leaf ⟨144182,18,(.group 5 2083 false)⟩))
(.branch 144218
(.leaf ⟨144200,18,(.group 5 2084 false)⟩)
(.leaf ⟨144218,18,(.group 5 2085 false)⟩))))))
(.branch 144524
(.branch 144380
(.branch 144308
(.branch 144272
(.branch 144254
(.leaf ⟨144236,18,(.group 5 2086 false)⟩)
(.leaf ⟨144254,18,(.group 5 2087 false)⟩))
(.branch 144290
(.leaf ⟨144272,18,(.group 5 2088 false)⟩)
(.leaf ⟨144290,18,(.group 5 2089 false)⟩)))
(.branch 144344
(.branch 144326
(.leaf ⟨144308,18,(.group 5 2090 false)⟩)
(.leaf ⟨144326,18,(.group 5 2091 false)⟩))
(.branch 144362
(.leaf ⟨144344,18,(.group 5 2092 false)⟩)
(.leaf ⟨144362,18,(.group 5 2093 false)⟩))))
(.branch 144452
(.branch 144416
(.branch 144398
(.leaf ⟨144380,18,(.group 5 2094 false)⟩)
(.leaf ⟨144398,18,(.group 5 2095 false)⟩))
(.branch 144434
(.leaf ⟨144416,18,(.group 5 2096 false)⟩)
(.leaf ⟨144434,18,(.group 5 2097 false)⟩)))
(.branch 144488
(.branch 144470
(.leaf ⟨144452,18,(.group 5 2098 false)⟩)
(.leaf ⟨144470,18,(.group 5 2099 false)⟩))
(.branch 144506
(.leaf ⟨144488,18,(.group 5 2100 false)⟩)
(.leaf ⟨144506,18,(.group 5 2101 false)⟩)))))
(.branch 144668
(.branch 144596
(.branch 144560
(.branch 144542
(.leaf ⟨144524,18,(.group 5 2102 false)⟩)
(.leaf ⟨144542,18,(.group 5 2103 false)⟩))
(.branch 144578
(.leaf ⟨144560,18,(.group 5 2104 false)⟩)
(.leaf ⟨144578,18,(.group 5 2105 false)⟩)))
(.branch 144632
(.branch 144614
(.leaf ⟨144596,18,(.group 5 2106 false)⟩)
(.leaf ⟨144614,18,(.group 5 2107 false)⟩))
(.branch 144650
(.leaf ⟨144632,18,(.group 5 2108 false)⟩)
(.leaf ⟨144650,18,(.group 5 2109 false)⟩))))
(.branch 144740
(.branch 144704
(.branch 144686
(.leaf ⟨144668,18,(.group 5 2110 false)⟩)
(.leaf ⟨144686,18,(.group 5 2111 false)⟩))
(.branch 144722
(.leaf ⟨144704,18,(.group 5 2112 false)⟩)
(.leaf ⟨144722,18,(.group 5 2113 false)⟩)))
(.branch 144776
(.branch 144758
(.leaf ⟨144740,18,(.group 5 2114 false)⟩)
(.leaf ⟨144758,18,(.group 5 2115 false)⟩))
(.branch 144794
(.leaf ⟨144776,18,(.group 5 2116 false)⟩)
(.leaf ⟨144794,18,(.group 5 2117 false)⟩)))))))

theorem tree143_checked : tree143.check 143660 144812 = true := by decide +kernel

def tree144 : Tree := (.branch 145388
(.branch 145100
(.branch 144956
(.branch 144884
(.branch 144848
(.branch 144830
(.leaf ⟨144812,18,(.group 5 2118 false)⟩)
(.leaf ⟨144830,18,(.group 5 2119 false)⟩))
(.branch 144866
(.leaf ⟨144848,18,(.group 5 2120 false)⟩)
(.leaf ⟨144866,18,(.group 5 2121 false)⟩)))
(.branch 144920
(.branch 144902
(.leaf ⟨144884,18,(.group 5 2122 false)⟩)
(.leaf ⟨144902,18,(.group 5 2123 false)⟩))
(.branch 144938
(.leaf ⟨144920,18,(.group 5 2124 false)⟩)
(.leaf ⟨144938,18,(.group 5 2125 false)⟩))))
(.branch 145028
(.branch 144992
(.branch 144974
(.leaf ⟨144956,18,(.group 5 2126 false)⟩)
(.leaf ⟨144974,18,(.group 5 2127 false)⟩))
(.branch 145010
(.leaf ⟨144992,18,(.group 5 2128 false)⟩)
(.leaf ⟨145010,18,(.group 5 2129 false)⟩)))
(.branch 145064
(.branch 145046
(.leaf ⟨145028,18,(.group 5 2130 false)⟩)
(.leaf ⟨145046,18,(.group 5 2131 false)⟩))
(.branch 145082
(.leaf ⟨145064,18,(.group 5 2132 false)⟩)
(.leaf ⟨145082,18,(.group 5 2133 false)⟩)))))
(.branch 145244
(.branch 145172
(.branch 145136
(.branch 145118
(.leaf ⟨145100,18,(.group 5 2134 false)⟩)
(.leaf ⟨145118,18,(.group 5 2135 false)⟩))
(.branch 145154
(.leaf ⟨145136,18,(.group 5 2136 false)⟩)
(.leaf ⟨145154,18,(.group 5 2137 false)⟩)))
(.branch 145208
(.branch 145190
(.leaf ⟨145172,18,(.group 5 2138 false)⟩)
(.leaf ⟨145190,18,(.group 5 2139 false)⟩))
(.branch 145226
(.leaf ⟨145208,18,(.group 5 2140 false)⟩)
(.leaf ⟨145226,18,(.group 5 2141 false)⟩))))
(.branch 145316
(.branch 145280
(.branch 145262
(.leaf ⟨145244,18,(.group 5 2142 false)⟩)
(.leaf ⟨145262,18,(.group 5 2143 false)⟩))
(.branch 145298
(.leaf ⟨145280,18,(.group 5 2144 false)⟩)
(.leaf ⟨145298,18,(.group 5 2145 false)⟩)))
(.branch 145352
(.branch 145334
(.leaf ⟨145316,18,(.group 5 2146 false)⟩)
(.leaf ⟨145334,18,(.group 5 2147 false)⟩))
(.branch 145370
(.leaf ⟨145352,18,(.group 5 2148 false)⟩)
(.leaf ⟨145370,18,(.group 5 2149 false)⟩))))))
(.branch 145676
(.branch 145532
(.branch 145460
(.branch 145424
(.branch 145406
(.leaf ⟨145388,18,(.group 5 2150 false)⟩)
(.leaf ⟨145406,18,(.group 5 2151 false)⟩))
(.branch 145442
(.leaf ⟨145424,18,(.group 5 2152 false)⟩)
(.leaf ⟨145442,18,(.group 5 2153 false)⟩)))
(.branch 145496
(.branch 145478
(.leaf ⟨145460,18,(.group 5 2154 false)⟩)
(.leaf ⟨145478,18,(.group 5 2155 false)⟩))
(.branch 145514
(.leaf ⟨145496,18,(.group 5 2156 false)⟩)
(.leaf ⟨145514,18,(.group 5 2157 false)⟩))))
(.branch 145604
(.branch 145568
(.branch 145550
(.leaf ⟨145532,18,(.group 5 2158 false)⟩)
(.leaf ⟨145550,18,(.group 5 2159 false)⟩))
(.branch 145586
(.leaf ⟨145568,18,(.group 5 2160 false)⟩)
(.leaf ⟨145586,18,(.group 5 2161 false)⟩)))
(.branch 145640
(.branch 145622
(.leaf ⟨145604,18,(.group 5 2162 false)⟩)
(.leaf ⟨145622,18,(.group 5 2163 false)⟩))
(.branch 145658
(.leaf ⟨145640,18,(.group 5 2164 false)⟩)
(.leaf ⟨145658,18,(.group 5 2165 false)⟩)))))
(.branch 145820
(.branch 145748
(.branch 145712
(.branch 145694
(.leaf ⟨145676,18,(.group 5 2166 false)⟩)
(.leaf ⟨145694,18,(.group 5 2167 false)⟩))
(.branch 145730
(.leaf ⟨145712,18,(.group 5 2168 false)⟩)
(.leaf ⟨145730,18,(.group 5 2169 false)⟩)))
(.branch 145784
(.branch 145766
(.leaf ⟨145748,18,(.group 5 2170 false)⟩)
(.leaf ⟨145766,18,(.group 5 2171 false)⟩))
(.branch 145802
(.leaf ⟨145784,18,(.group 5 2172 false)⟩)
(.leaf ⟨145802,18,(.group 5 2173 false)⟩))))
(.branch 145892
(.branch 145856
(.branch 145838
(.leaf ⟨145820,18,(.group 5 2174 false)⟩)
(.leaf ⟨145838,18,(.group 5 2175 false)⟩))
(.branch 145874
(.leaf ⟨145856,18,(.group 5 2176 false)⟩)
(.leaf ⟨145874,18,(.group 5 2177 false)⟩)))
(.branch 145928
(.branch 145910
(.leaf ⟨145892,18,(.group 5 2178 false)⟩)
(.leaf ⟨145910,18,(.group 5 2179 false)⟩))
(.branch 145946
(.leaf ⟨145928,18,(.group 5 2180 false)⟩)
(.leaf ⟨145946,18,(.group 5 2181 false)⟩)))))))

theorem tree144_checked : tree144.check 144812 145964 = true := by decide +kernel

def tree145 : Tree := (.branch 146540
(.branch 146252
(.branch 146108
(.branch 146036
(.branch 146000
(.branch 145982
(.leaf ⟨145964,18,(.group 5 2182 false)⟩)
(.leaf ⟨145982,18,(.group 5 2183 false)⟩))
(.branch 146018
(.leaf ⟨146000,18,(.group 5 2184 false)⟩)
(.leaf ⟨146018,18,(.group 5 2185 false)⟩)))
(.branch 146072
(.branch 146054
(.leaf ⟨146036,18,(.group 5 2186 false)⟩)
(.leaf ⟨146054,18,(.group 5 2187 false)⟩))
(.branch 146090
(.leaf ⟨146072,18,(.group 5 2188 false)⟩)
(.leaf ⟨146090,18,(.group 5 2189 false)⟩))))
(.branch 146180
(.branch 146144
(.branch 146126
(.leaf ⟨146108,18,(.group 5 2190 false)⟩)
(.leaf ⟨146126,18,(.group 5 2191 false)⟩))
(.branch 146162
(.leaf ⟨146144,18,(.group 5 2192 false)⟩)
(.leaf ⟨146162,18,(.group 5 2193 false)⟩)))
(.branch 146216
(.branch 146198
(.leaf ⟨146180,18,(.group 5 2194 false)⟩)
(.leaf ⟨146198,18,(.group 5 2195 false)⟩))
(.branch 146234
(.leaf ⟨146216,18,(.group 5 2196 false)⟩)
(.leaf ⟨146234,18,(.group 5 2197 false)⟩)))))
(.branch 146396
(.branch 146324
(.branch 146288
(.branch 146270
(.leaf ⟨146252,18,(.group 5 2198 false)⟩)
(.leaf ⟨146270,18,(.group 5 2199 false)⟩))
(.branch 146306
(.leaf ⟨146288,18,(.group 5 2200 false)⟩)
(.leaf ⟨146306,18,(.group 5 2201 false)⟩)))
(.branch 146360
(.branch 146342
(.leaf ⟨146324,18,(.group 5 2202 false)⟩)
(.leaf ⟨146342,18,(.group 5 2203 false)⟩))
(.branch 146378
(.leaf ⟨146360,18,(.group 5 2204 false)⟩)
(.leaf ⟨146378,18,(.group 5 2205 false)⟩))))
(.branch 146468
(.branch 146432
(.branch 146414
(.leaf ⟨146396,18,(.group 5 2206 false)⟩)
(.leaf ⟨146414,18,(.group 5 2207 false)⟩))
(.branch 146450
(.leaf ⟨146432,18,(.group 5 2208 false)⟩)
(.leaf ⟨146450,18,(.group 5 2209 false)⟩)))
(.branch 146504
(.branch 146486
(.leaf ⟨146468,18,(.group 5 2210 false)⟩)
(.leaf ⟨146486,18,(.group 5 2211 false)⟩))
(.branch 146522
(.leaf ⟨146504,18,(.group 5 2212 false)⟩)
(.leaf ⟨146522,18,(.group 5 2213 false)⟩))))))
(.branch 146828
(.branch 146684
(.branch 146612
(.branch 146576
(.branch 146558
(.leaf ⟨146540,18,(.group 5 2214 false)⟩)
(.leaf ⟨146558,18,(.group 5 2215 false)⟩))
(.branch 146594
(.leaf ⟨146576,18,(.group 5 2216 false)⟩)
(.leaf ⟨146594,18,(.group 5 2217 false)⟩)))
(.branch 146648
(.branch 146630
(.leaf ⟨146612,18,(.group 5 2218 false)⟩)
(.leaf ⟨146630,18,(.group 5 2219 false)⟩))
(.branch 146666
(.leaf ⟨146648,18,(.group 5 2220 false)⟩)
(.leaf ⟨146666,18,(.group 5 2221 false)⟩))))
(.branch 146756
(.branch 146720
(.branch 146702
(.leaf ⟨146684,18,(.group 5 2222 false)⟩)
(.leaf ⟨146702,18,(.group 5 2223 false)⟩))
(.branch 146738
(.leaf ⟨146720,18,(.group 5 2224 false)⟩)
(.leaf ⟨146738,18,(.group 5 2225 false)⟩)))
(.branch 146792
(.branch 146774
(.leaf ⟨146756,18,(.group 5 2226 false)⟩)
(.leaf ⟨146774,18,(.group 5 2227 false)⟩))
(.branch 146810
(.leaf ⟨146792,18,(.group 5 2228 false)⟩)
(.leaf ⟨146810,18,(.group 5 2229 false)⟩)))))
(.branch 146972
(.branch 146900
(.branch 146864
(.branch 146846
(.leaf ⟨146828,18,(.group 5 2230 false)⟩)
(.leaf ⟨146846,18,(.group 5 2231 false)⟩))
(.branch 146882
(.leaf ⟨146864,18,(.group 5 2232 false)⟩)
(.leaf ⟨146882,18,(.group 5 2233 false)⟩)))
(.branch 146936
(.branch 146918
(.leaf ⟨146900,18,(.group 5 2234 false)⟩)
(.leaf ⟨146918,18,(.group 5 2235 false)⟩))
(.branch 146954
(.leaf ⟨146936,18,(.group 5 2236 false)⟩)
(.leaf ⟨146954,18,(.group 5 2237 false)⟩))))
(.branch 147044
(.branch 147008
(.branch 146990
(.leaf ⟨146972,18,(.group 5 2238 false)⟩)
(.leaf ⟨146990,18,(.group 5 2239 false)⟩))
(.branch 147026
(.leaf ⟨147008,18,(.group 5 2240 false)⟩)
(.leaf ⟨147026,18,(.group 5 2241 false)⟩)))
(.branch 147080
(.branch 147062
(.leaf ⟨147044,18,(.group 5 2242 false)⟩)
(.leaf ⟨147062,18,(.group 5 2243 false)⟩))
(.branch 147098
(.leaf ⟨147080,18,(.group 5 2244 false)⟩)
(.leaf ⟨147098,18,(.group 5 2245 false)⟩)))))))

theorem tree145_checked : tree145.check 145964 147116 = true := by decide +kernel

def tree146 : Tree := (.branch 147692
(.branch 147404
(.branch 147260
(.branch 147188
(.branch 147152
(.branch 147134
(.leaf ⟨147116,18,(.group 5 2246 false)⟩)
(.leaf ⟨147134,18,(.group 5 2247 false)⟩))
(.branch 147170
(.leaf ⟨147152,18,(.group 5 2248 false)⟩)
(.leaf ⟨147170,18,(.group 5 2249 false)⟩)))
(.branch 147224
(.branch 147206
(.leaf ⟨147188,18,(.group 5 2250 false)⟩)
(.leaf ⟨147206,18,(.group 5 2251 false)⟩))
(.branch 147242
(.leaf ⟨147224,18,(.group 5 2252 false)⟩)
(.leaf ⟨147242,18,(.group 5 2253 false)⟩))))
(.branch 147332
(.branch 147296
(.branch 147278
(.leaf ⟨147260,18,(.group 5 2254 false)⟩)
(.leaf ⟨147278,18,(.group 5 2255 false)⟩))
(.branch 147314
(.leaf ⟨147296,18,(.group 5 2256 false)⟩)
(.leaf ⟨147314,18,(.group 5 2257 false)⟩)))
(.branch 147368
(.branch 147350
(.leaf ⟨147332,18,(.group 5 2258 false)⟩)
(.leaf ⟨147350,18,(.group 5 2259 false)⟩))
(.branch 147386
(.leaf ⟨147368,18,(.group 5 2260 false)⟩)
(.leaf ⟨147386,18,(.group 5 2261 false)⟩)))))
(.branch 147548
(.branch 147476
(.branch 147440
(.branch 147422
(.leaf ⟨147404,18,(.group 5 2262 false)⟩)
(.leaf ⟨147422,18,(.group 5 2263 false)⟩))
(.branch 147458
(.leaf ⟨147440,18,(.group 5 2264 false)⟩)
(.leaf ⟨147458,18,(.group 5 2265 false)⟩)))
(.branch 147512
(.branch 147494
(.leaf ⟨147476,18,(.group 5 2266 false)⟩)
(.leaf ⟨147494,18,(.group 5 2267 false)⟩))
(.branch 147530
(.leaf ⟨147512,18,(.group 5 2268 false)⟩)
(.leaf ⟨147530,18,(.group 5 2269 false)⟩))))
(.branch 147620
(.branch 147584
(.branch 147566
(.leaf ⟨147548,18,(.group 5 2270 false)⟩)
(.leaf ⟨147566,18,(.group 5 2271 false)⟩))
(.branch 147602
(.leaf ⟨147584,18,(.group 5 2272 false)⟩)
(.leaf ⟨147602,18,(.group 5 2273 false)⟩)))
(.branch 147656
(.branch 147638
(.leaf ⟨147620,18,(.group 5 2274 false)⟩)
(.leaf ⟨147638,18,(.group 5 2275 false)⟩))
(.branch 147674
(.leaf ⟨147656,18,(.group 5 2276 false)⟩)
(.leaf ⟨147674,18,(.group 5 2277 false)⟩))))))
(.branch 147980
(.branch 147836
(.branch 147764
(.branch 147728
(.branch 147710
(.leaf ⟨147692,18,(.group 5 2278 false)⟩)
(.leaf ⟨147710,18,(.group 5 2279 false)⟩))
(.branch 147746
(.leaf ⟨147728,18,(.group 5 2280 false)⟩)
(.leaf ⟨147746,18,(.group 5 2281 false)⟩)))
(.branch 147800
(.branch 147782
(.leaf ⟨147764,18,(.group 5 2282 false)⟩)
(.leaf ⟨147782,18,(.group 5 2283 false)⟩))
(.branch 147818
(.leaf ⟨147800,18,(.group 5 2284 false)⟩)
(.leaf ⟨147818,18,(.group 5 2285 false)⟩))))
(.branch 147908
(.branch 147872
(.branch 147854
(.leaf ⟨147836,18,(.group 5 2286 false)⟩)
(.leaf ⟨147854,18,(.group 5 2287 false)⟩))
(.branch 147890
(.leaf ⟨147872,18,(.group 5 2288 false)⟩)
(.leaf ⟨147890,18,(.group 5 2289 false)⟩)))
(.branch 147944
(.branch 147926
(.leaf ⟨147908,18,(.group 5 2290 false)⟩)
(.leaf ⟨147926,18,(.group 5 2291 false)⟩))
(.branch 147962
(.leaf ⟨147944,18,(.group 5 2292 false)⟩)
(.leaf ⟨147962,18,(.group 5 2293 false)⟩)))))
(.branch 148124
(.branch 148052
(.branch 148016
(.branch 147998
(.leaf ⟨147980,18,(.group 5 2294 false)⟩)
(.leaf ⟨147998,18,(.group 5 2295 false)⟩))
(.branch 148034
(.leaf ⟨148016,18,(.group 5 2296 false)⟩)
(.leaf ⟨148034,18,(.group 5 2297 false)⟩)))
(.branch 148088
(.branch 148070
(.leaf ⟨148052,18,(.group 5 2298 false)⟩)
(.leaf ⟨148070,18,(.group 5 2299 false)⟩))
(.branch 148106
(.leaf ⟨148088,18,(.group 5 2300 false)⟩)
(.leaf ⟨148106,18,(.group 5 2301 false)⟩))))
(.branch 148196
(.branch 148160
(.branch 148142
(.leaf ⟨148124,18,(.group 5 2302 false)⟩)
(.leaf ⟨148142,18,(.group 5 2303 false)⟩))
(.branch 148178
(.leaf ⟨148160,18,(.group 5 2304 false)⟩)
(.leaf ⟨148178,18,(.group 5 2305 false)⟩)))
(.branch 148232
(.branch 148214
(.leaf ⟨148196,18,(.group 5 2306 false)⟩)
(.leaf ⟨148214,18,(.group 5 2307 false)⟩))
(.branch 148250
(.leaf ⟨148232,18,(.group 5 2308 false)⟩)
(.leaf ⟨148250,18,(.group 5 2309 false)⟩)))))))

theorem tree146_checked : tree146.check 147116 148268 = true := by decide +kernel

def tree147 : Tree := (.branch 148844
(.branch 148556
(.branch 148412
(.branch 148340
(.branch 148304
(.branch 148286
(.leaf ⟨148268,18,(.group 5 2310 false)⟩)
(.leaf ⟨148286,18,(.group 5 2311 false)⟩))
(.branch 148322
(.leaf ⟨148304,18,(.group 5 2312 false)⟩)
(.leaf ⟨148322,18,(.group 5 2313 false)⟩)))
(.branch 148376
(.branch 148358
(.leaf ⟨148340,18,(.group 5 2314 false)⟩)
(.leaf ⟨148358,18,(.group 5 2315 false)⟩))
(.branch 148394
(.leaf ⟨148376,18,(.group 5 2316 false)⟩)
(.leaf ⟨148394,18,(.group 5 2317 false)⟩))))
(.branch 148484
(.branch 148448
(.branch 148430
(.leaf ⟨148412,18,(.group 5 2318 false)⟩)
(.leaf ⟨148430,18,(.group 5 2319 false)⟩))
(.branch 148466
(.leaf ⟨148448,18,(.group 5 2320 false)⟩)
(.leaf ⟨148466,18,(.group 5 2321 false)⟩)))
(.branch 148520
(.branch 148502
(.leaf ⟨148484,18,(.group 5 2322 false)⟩)
(.leaf ⟨148502,18,(.group 5 2323 false)⟩))
(.branch 148538
(.leaf ⟨148520,18,(.group 5 2324 false)⟩)
(.leaf ⟨148538,18,(.group 5 2325 false)⟩)))))
(.branch 148700
(.branch 148628
(.branch 148592
(.branch 148574
(.leaf ⟨148556,18,(.group 5 2326 false)⟩)
(.leaf ⟨148574,18,(.group 5 2327 false)⟩))
(.branch 148610
(.leaf ⟨148592,18,(.group 5 2328 false)⟩)
(.leaf ⟨148610,18,(.group 5 2329 false)⟩)))
(.branch 148664
(.branch 148646
(.leaf ⟨148628,18,(.group 5 2330 false)⟩)
(.leaf ⟨148646,18,(.group 5 2331 false)⟩))
(.branch 148682
(.leaf ⟨148664,18,(.group 5 2332 false)⟩)
(.leaf ⟨148682,18,(.group 5 2333 false)⟩))))
(.branch 148772
(.branch 148736
(.branch 148718
(.leaf ⟨148700,18,(.group 6 1302 false)⟩)
(.leaf ⟨148718,18,(.group 6 1303 false)⟩))
(.branch 148754
(.leaf ⟨148736,18,(.group 6 1304 false)⟩)
(.leaf ⟨148754,18,(.group 6 1305 false)⟩)))
(.branch 148808
(.branch 148790
(.leaf ⟨148772,18,(.group 6 1306 false)⟩)
(.leaf ⟨148790,18,(.group 6 1307 false)⟩))
(.branch 148826
(.leaf ⟨148808,18,(.group 6 1308 false)⟩)
(.leaf ⟨148826,18,(.group 6 1309 false)⟩))))))
(.branch 149132
(.branch 148988
(.branch 148916
(.branch 148880
(.branch 148862
(.leaf ⟨148844,18,(.group 6 1310 false)⟩)
(.leaf ⟨148862,18,(.group 6 1311 false)⟩))
(.branch 148898
(.leaf ⟨148880,18,(.group 6 1312 false)⟩)
(.leaf ⟨148898,18,(.group 6 1313 false)⟩)))
(.branch 148952
(.branch 148934
(.leaf ⟨148916,18,(.group 6 1314 false)⟩)
(.leaf ⟨148934,18,(.group 6 1315 false)⟩))
(.branch 148970
(.leaf ⟨148952,18,(.group 6 1316 false)⟩)
(.leaf ⟨148970,18,(.group 6 1317 false)⟩))))
(.branch 149060
(.branch 149024
(.branch 149006
(.leaf ⟨148988,18,(.group 6 1318 false)⟩)
(.leaf ⟨149006,18,(.group 6 1319 false)⟩))
(.branch 149042
(.leaf ⟨149024,18,(.group 6 1320 false)⟩)
(.leaf ⟨149042,18,(.group 6 1321 false)⟩)))
(.branch 149096
(.branch 149078
(.leaf ⟨149060,18,(.group 6 1322 false)⟩)
(.leaf ⟨149078,18,(.group 6 1323 false)⟩))
(.branch 149114
(.leaf ⟨149096,18,(.group 6 1324 false)⟩)
(.leaf ⟨149114,18,(.group 6 1325 false)⟩)))))
(.branch 149276
(.branch 149204
(.branch 149168
(.branch 149150
(.leaf ⟨149132,18,(.group 6 1326 false)⟩)
(.leaf ⟨149150,18,(.group 6 1327 false)⟩))
(.branch 149186
(.leaf ⟨149168,18,(.group 6 1328 false)⟩)
(.leaf ⟨149186,18,(.group 6 1329 false)⟩)))
(.branch 149240
(.branch 149222
(.leaf ⟨149204,18,(.group 6 1330 false)⟩)
(.leaf ⟨149222,18,(.group 6 1331 false)⟩))
(.branch 149258
(.leaf ⟨149240,18,(.group 6 1332 false)⟩)
(.leaf ⟨149258,18,(.group 6 1333 false)⟩))))
(.branch 149348
(.branch 149312
(.branch 149294
(.leaf ⟨149276,18,(.group 6 1334 false)⟩)
(.leaf ⟨149294,18,(.group 6 1335 false)⟩))
(.branch 149330
(.leaf ⟨149312,18,(.group 6 1336 false)⟩)
(.leaf ⟨149330,18,(.group 6 1337 false)⟩)))
(.branch 149384
(.branch 149366
(.leaf ⟨149348,18,(.group 6 1338 false)⟩)
(.leaf ⟨149366,18,(.group 6 1339 false)⟩))
(.branch 149402
(.leaf ⟨149384,18,(.group 6 1340 false)⟩)
(.leaf ⟨149402,18,(.group 6 1341 false)⟩)))))))

theorem tree147_checked : tree147.check 148268 149420 = true := by decide +kernel

def tree148 : Tree := (.branch 149996
(.branch 149708
(.branch 149564
(.branch 149492
(.branch 149456
(.branch 149438
(.leaf ⟨149420,18,(.group 6 1342 false)⟩)
(.leaf ⟨149438,18,(.group 6 1343 false)⟩))
(.branch 149474
(.leaf ⟨149456,18,(.group 6 1344 false)⟩)
(.leaf ⟨149474,18,(.group 6 1345 false)⟩)))
(.branch 149528
(.branch 149510
(.leaf ⟨149492,18,(.group 6 1346 false)⟩)
(.leaf ⟨149510,18,(.group 6 1347 false)⟩))
(.branch 149546
(.leaf ⟨149528,18,(.group 6 1348 false)⟩)
(.leaf ⟨149546,18,(.group 6 1349 false)⟩))))
(.branch 149636
(.branch 149600
(.branch 149582
(.leaf ⟨149564,18,(.group 6 1350 false)⟩)
(.leaf ⟨149582,18,(.group 6 1351 false)⟩))
(.branch 149618
(.leaf ⟨149600,18,(.group 6 1352 false)⟩)
(.leaf ⟨149618,18,(.group 6 1353 false)⟩)))
(.branch 149672
(.branch 149654
(.leaf ⟨149636,18,(.group 6 1354 false)⟩)
(.leaf ⟨149654,18,(.group 6 1355 false)⟩))
(.branch 149690
(.leaf ⟨149672,18,(.group 6 1356 false)⟩)
(.leaf ⟨149690,18,(.group 6 1357 false)⟩)))))
(.branch 149852
(.branch 149780
(.branch 149744
(.branch 149726
(.leaf ⟨149708,18,(.group 6 1358 false)⟩)
(.leaf ⟨149726,18,(.group 6 1359 false)⟩))
(.branch 149762
(.leaf ⟨149744,18,(.group 6 1360 false)⟩)
(.leaf ⟨149762,18,(.group 6 1361 false)⟩)))
(.branch 149816
(.branch 149798
(.leaf ⟨149780,18,(.group 6 1362 false)⟩)
(.leaf ⟨149798,18,(.group 6 1363 false)⟩))
(.branch 149834
(.leaf ⟨149816,18,(.group 6 1364 false)⟩)
(.leaf ⟨149834,18,(.group 6 1365 false)⟩))))
(.branch 149924
(.branch 149888
(.branch 149870
(.leaf ⟨149852,18,(.group 6 1366 false)⟩)
(.leaf ⟨149870,18,(.group 6 1367 false)⟩))
(.branch 149906
(.leaf ⟨149888,18,(.group 6 1368 false)⟩)
(.leaf ⟨149906,18,(.group 6 1369 false)⟩)))
(.branch 149960
(.branch 149942
(.leaf ⟨149924,18,(.group 6 1370 false)⟩)
(.leaf ⟨149942,18,(.group 6 1371 false)⟩))
(.branch 149978
(.leaf ⟨149960,18,(.group 6 1372 false)⟩)
(.leaf ⟨149978,18,(.group 6 1373 false)⟩))))))
(.branch 150284
(.branch 150140
(.branch 150068
(.branch 150032
(.branch 150014
(.leaf ⟨149996,18,(.group 6 1374 false)⟩)
(.leaf ⟨150014,18,(.group 6 1375 false)⟩))
(.branch 150050
(.leaf ⟨150032,18,(.group 6 1376 false)⟩)
(.leaf ⟨150050,18,(.group 6 1377 false)⟩)))
(.branch 150104
(.branch 150086
(.leaf ⟨150068,18,(.group 6 1378 false)⟩)
(.leaf ⟨150086,18,(.group 6 1379 false)⟩))
(.branch 150122
(.leaf ⟨150104,18,(.group 6 1380 false)⟩)
(.leaf ⟨150122,18,(.group 6 1381 false)⟩))))
(.branch 150212
(.branch 150176
(.branch 150158
(.leaf ⟨150140,18,(.group 6 1382 false)⟩)
(.leaf ⟨150158,18,(.group 6 1383 false)⟩))
(.branch 150194
(.leaf ⟨150176,18,(.group 6 1384 false)⟩)
(.leaf ⟨150194,18,(.group 6 1385 false)⟩)))
(.branch 150248
(.branch 150230
(.leaf ⟨150212,18,(.group 6 1386 false)⟩)
(.leaf ⟨150230,18,(.group 6 1387 false)⟩))
(.branch 150266
(.leaf ⟨150248,18,(.group 6 1388 false)⟩)
(.leaf ⟨150266,18,(.group 6 1389 false)⟩)))))
(.branch 150428
(.branch 150356
(.branch 150320
(.branch 150302
(.leaf ⟨150284,18,(.group 6 1390 false)⟩)
(.leaf ⟨150302,18,(.group 6 1391 false)⟩))
(.branch 150338
(.leaf ⟨150320,18,(.group 6 1392 false)⟩)
(.leaf ⟨150338,18,(.group 6 1393 false)⟩)))
(.branch 150392
(.branch 150374
(.leaf ⟨150356,18,(.group 6 1394 false)⟩)
(.leaf ⟨150374,18,(.group 6 1395 false)⟩))
(.branch 150410
(.leaf ⟨150392,18,(.group 6 1396 false)⟩)
(.leaf ⟨150410,18,(.group 6 1397 false)⟩))))
(.branch 150500
(.branch 150464
(.branch 150446
(.leaf ⟨150428,18,(.group 6 1398 false)⟩)
(.leaf ⟨150446,18,(.group 6 1399 false)⟩))
(.branch 150482
(.leaf ⟨150464,18,(.group 6 1400 false)⟩)
(.leaf ⟨150482,18,(.group 6 1401 false)⟩)))
(.branch 150536
(.branch 150518
(.leaf ⟨150500,18,(.group 6 1402 false)⟩)
(.leaf ⟨150518,18,(.group 6 1403 false)⟩))
(.branch 150554
(.leaf ⟨150536,18,(.group 6 1404 false)⟩)
(.leaf ⟨150554,18,(.group 6 1405 false)⟩)))))))

theorem tree148_checked : tree148.check 149420 150572 = true := by decide +kernel

def tree149 : Tree := (.branch 151148
(.branch 150860
(.branch 150716
(.branch 150644
(.branch 150608
(.branch 150590
(.leaf ⟨150572,18,(.group 6 1406 false)⟩)
(.leaf ⟨150590,18,(.group 6 1407 false)⟩))
(.branch 150626
(.leaf ⟨150608,18,(.group 6 1408 false)⟩)
(.leaf ⟨150626,18,(.group 6 1409 false)⟩)))
(.branch 150680
(.branch 150662
(.leaf ⟨150644,18,(.group 6 1410 false)⟩)
(.leaf ⟨150662,18,(.group 6 1411 false)⟩))
(.branch 150698
(.leaf ⟨150680,18,(.group 6 1412 false)⟩)
(.leaf ⟨150698,18,(.group 6 1413 false)⟩))))
(.branch 150788
(.branch 150752
(.branch 150734
(.leaf ⟨150716,18,(.group 6 1414 false)⟩)
(.leaf ⟨150734,18,(.group 6 1415 false)⟩))
(.branch 150770
(.leaf ⟨150752,18,(.group 6 1416 false)⟩)
(.leaf ⟨150770,18,(.group 6 1417 false)⟩)))
(.branch 150824
(.branch 150806
(.leaf ⟨150788,18,(.group 6 1418 false)⟩)
(.leaf ⟨150806,18,(.group 6 1419 false)⟩))
(.branch 150842
(.leaf ⟨150824,18,(.group 6 1420 false)⟩)
(.leaf ⟨150842,18,(.group 6 1421 false)⟩)))))
(.branch 151004
(.branch 150932
(.branch 150896
(.branch 150878
(.leaf ⟨150860,18,(.group 6 1422 false)⟩)
(.leaf ⟨150878,18,(.group 6 1423 false)⟩))
(.branch 150914
(.leaf ⟨150896,18,(.group 6 1424 false)⟩)
(.leaf ⟨150914,18,(.group 6 1425 false)⟩)))
(.branch 150968
(.branch 150950
(.leaf ⟨150932,18,(.group 6 1426 false)⟩)
(.leaf ⟨150950,18,(.group 6 1427 false)⟩))
(.branch 150986
(.leaf ⟨150968,18,(.group 6 1428 false)⟩)
(.leaf ⟨150986,18,(.group 6 1429 false)⟩))))
(.branch 151076
(.branch 151040
(.branch 151022
(.leaf ⟨151004,18,(.group 6 1430 false)⟩)
(.leaf ⟨151022,18,(.group 6 1431 false)⟩))
(.branch 151058
(.leaf ⟨151040,18,(.group 6 1432 false)⟩)
(.leaf ⟨151058,18,(.group 6 1433 false)⟩)))
(.branch 151112
(.branch 151094
(.leaf ⟨151076,18,(.group 6 1434 false)⟩)
(.leaf ⟨151094,18,(.group 6 1435 false)⟩))
(.branch 151130
(.leaf ⟨151112,18,(.group 6 1436 false)⟩)
(.leaf ⟨151130,18,(.group 6 1437 false)⟩))))))
(.branch 151436
(.branch 151292
(.branch 151220
(.branch 151184
(.branch 151166
(.leaf ⟨151148,18,(.group 6 1438 false)⟩)
(.leaf ⟨151166,18,(.group 6 1439 false)⟩))
(.branch 151202
(.leaf ⟨151184,18,(.group 6 1440 false)⟩)
(.leaf ⟨151202,18,(.group 6 1441 false)⟩)))
(.branch 151256
(.branch 151238
(.leaf ⟨151220,18,(.group 6 1442 false)⟩)
(.leaf ⟨151238,18,(.group 6 1443 false)⟩))
(.branch 151274
(.leaf ⟨151256,18,(.group 6 1444 false)⟩)
(.leaf ⟨151274,18,(.group 6 1445 false)⟩))))
(.branch 151364
(.branch 151328
(.branch 151310
(.leaf ⟨151292,18,(.group 6 1446 false)⟩)
(.leaf ⟨151310,18,(.group 6 1447 false)⟩))
(.branch 151346
(.leaf ⟨151328,18,(.group 6 1448 false)⟩)
(.leaf ⟨151346,18,(.group 6 1449 false)⟩)))
(.branch 151400
(.branch 151382
(.leaf ⟨151364,18,(.group 6 1450 false)⟩)
(.leaf ⟨151382,18,(.group 6 1451 false)⟩))
(.branch 151418
(.leaf ⟨151400,18,(.group 6 1452 false)⟩)
(.leaf ⟨151418,18,(.group 6 1453 false)⟩)))))
(.branch 151580
(.branch 151508
(.branch 151472
(.branch 151454
(.leaf ⟨151436,18,(.group 6 1454 false)⟩)
(.leaf ⟨151454,18,(.group 6 1455 false)⟩))
(.branch 151490
(.leaf ⟨151472,18,(.group 6 1456 false)⟩)
(.leaf ⟨151490,18,(.group 6 1457 false)⟩)))
(.branch 151544
(.branch 151526
(.leaf ⟨151508,18,(.group 6 1458 false)⟩)
(.leaf ⟨151526,18,(.group 6 1459 false)⟩))
(.branch 151562
(.leaf ⟨151544,18,(.group 6 1460 false)⟩)
(.leaf ⟨151562,18,(.group 6 1461 false)⟩))))
(.branch 151652
(.branch 151616
(.branch 151598
(.leaf ⟨151580,18,(.group 6 1462 false)⟩)
(.leaf ⟨151598,18,(.group 6 1463 false)⟩))
(.branch 151634
(.leaf ⟨151616,18,(.group 6 1464 false)⟩)
(.leaf ⟨151634,18,(.group 6 1465 false)⟩)))
(.branch 151688
(.branch 151670
(.leaf ⟨151652,18,(.group 6 1466 false)⟩)
(.leaf ⟨151670,18,(.group 6 1467 false)⟩))
(.branch 151706
(.leaf ⟨151688,18,(.group 6 1468 false)⟩)
(.leaf ⟨151706,18,(.group 6 1469 false)⟩)))))))

theorem tree149_checked : tree149.check 150572 151724 = true := by decide +kernel

def tree150 : Tree := (.branch 152300
(.branch 152012
(.branch 151868
(.branch 151796
(.branch 151760
(.branch 151742
(.leaf ⟨151724,18,(.group 6 1470 false)⟩)
(.leaf ⟨151742,18,(.group 6 1471 false)⟩))
(.branch 151778
(.leaf ⟨151760,18,(.group 6 1472 false)⟩)
(.leaf ⟨151778,18,(.group 6 1473 false)⟩)))
(.branch 151832
(.branch 151814
(.leaf ⟨151796,18,(.group 6 1474 false)⟩)
(.leaf ⟨151814,18,(.group 6 1475 false)⟩))
(.branch 151850
(.leaf ⟨151832,18,(.group 6 1476 false)⟩)
(.leaf ⟨151850,18,(.group 6 1477 false)⟩))))
(.branch 151940
(.branch 151904
(.branch 151886
(.leaf ⟨151868,18,(.group 6 1478 false)⟩)
(.leaf ⟨151886,18,(.group 6 1479 false)⟩))
(.branch 151922
(.leaf ⟨151904,18,(.group 6 1480 false)⟩)
(.leaf ⟨151922,18,(.group 6 1481 false)⟩)))
(.branch 151976
(.branch 151958
(.leaf ⟨151940,18,(.group 6 1482 false)⟩)
(.leaf ⟨151958,18,(.group 6 1483 false)⟩))
(.branch 151994
(.leaf ⟨151976,18,(.group 6 1484 false)⟩)
(.leaf ⟨151994,18,(.group 6 1485 false)⟩)))))
(.branch 152156
(.branch 152084
(.branch 152048
(.branch 152030
(.leaf ⟨152012,18,(.group 6 1486 false)⟩)
(.leaf ⟨152030,18,(.group 6 1487 false)⟩))
(.branch 152066
(.leaf ⟨152048,18,(.group 6 1488 false)⟩)
(.leaf ⟨152066,18,(.group 6 1489 false)⟩)))
(.branch 152120
(.branch 152102
(.leaf ⟨152084,18,(.group 6 1490 false)⟩)
(.leaf ⟨152102,18,(.group 6 1491 false)⟩))
(.branch 152138
(.leaf ⟨152120,18,(.group 6 1492 false)⟩)
(.leaf ⟨152138,18,(.group 6 1493 false)⟩))))
(.branch 152228
(.branch 152192
(.branch 152174
(.leaf ⟨152156,18,(.group 6 1494 false)⟩)
(.leaf ⟨152174,18,(.group 6 1495 false)⟩))
(.branch 152210
(.leaf ⟨152192,18,(.group 6 1496 false)⟩)
(.leaf ⟨152210,18,(.group 6 1497 false)⟩)))
(.branch 152264
(.branch 152246
(.leaf ⟨152228,18,(.group 6 1498 false)⟩)
(.leaf ⟨152246,18,(.group 6 1499 false)⟩))
(.branch 152282
(.leaf ⟨152264,18,(.group 6 1500 false)⟩)
(.leaf ⟨152282,18,(.group 6 1501 false)⟩))))))
(.branch 152588
(.branch 152444
(.branch 152372
(.branch 152336
(.branch 152318
(.leaf ⟨152300,18,(.group 6 1502 false)⟩)
(.leaf ⟨152318,18,(.group 6 1503 false)⟩))
(.branch 152354
(.leaf ⟨152336,18,(.group 6 1504 false)⟩)
(.leaf ⟨152354,18,(.group 6 1505 false)⟩)))
(.branch 152408
(.branch 152390
(.leaf ⟨152372,18,(.group 6 1506 false)⟩)
(.leaf ⟨152390,18,(.group 6 1507 false)⟩))
(.branch 152426
(.leaf ⟨152408,18,(.group 6 1508 false)⟩)
(.leaf ⟨152426,18,(.group 6 1509 false)⟩))))
(.branch 152516
(.branch 152480
(.branch 152462
(.leaf ⟨152444,18,(.group 6 1510 false)⟩)
(.leaf ⟨152462,18,(.group 6 1511 false)⟩))
(.branch 152498
(.leaf ⟨152480,18,(.group 6 1512 false)⟩)
(.leaf ⟨152498,18,(.group 6 1513 false)⟩)))
(.branch 152552
(.branch 152534
(.leaf ⟨152516,18,(.group 6 1514 false)⟩)
(.leaf ⟨152534,18,(.group 6 1515 false)⟩))
(.branch 152570
(.leaf ⟨152552,18,(.group 6 1516 false)⟩)
(.leaf ⟨152570,18,(.group 6 1517 false)⟩)))))
(.branch 152732
(.branch 152660
(.branch 152624
(.branch 152606
(.leaf ⟨152588,18,(.group 6 1518 false)⟩)
(.leaf ⟨152606,18,(.group 6 1519 false)⟩))
(.branch 152642
(.leaf ⟨152624,18,(.group 6 1520 false)⟩)
(.leaf ⟨152642,18,(.group 6 1521 false)⟩)))
(.branch 152696
(.branch 152678
(.leaf ⟨152660,18,(.group 6 1522 false)⟩)
(.leaf ⟨152678,18,(.group 6 1523 false)⟩))
(.branch 152714
(.leaf ⟨152696,18,(.group 6 1524 false)⟩)
(.leaf ⟨152714,18,(.group 6 1525 false)⟩))))
(.branch 152804
(.branch 152768
(.branch 152750
(.leaf ⟨152732,18,(.group 6 1526 false)⟩)
(.leaf ⟨152750,18,(.group 6 1527 false)⟩))
(.branch 152786
(.leaf ⟨152768,18,(.group 6 1528 false)⟩)
(.leaf ⟨152786,18,(.group 6 1529 false)⟩)))
(.branch 152840
(.branch 152822
(.leaf ⟨152804,18,(.group 6 1530 false)⟩)
(.leaf ⟨152822,18,(.group 6 1531 false)⟩))
(.branch 152858
(.leaf ⟨152840,18,(.group 6 1532 false)⟩)
(.leaf ⟨152858,18,(.group 6 1533 false)⟩)))))))

theorem tree150_checked : tree150.check 151724 152876 = true := by decide +kernel

def tree151 : Tree := (.branch 153452
(.branch 153164
(.branch 153020
(.branch 152948
(.branch 152912
(.branch 152894
(.leaf ⟨152876,18,(.group 6 1534 false)⟩)
(.leaf ⟨152894,18,(.group 6 1535 false)⟩))
(.branch 152930
(.leaf ⟨152912,18,(.group 6 1536 false)⟩)
(.leaf ⟨152930,18,(.group 6 1537 false)⟩)))
(.branch 152984
(.branch 152966
(.leaf ⟨152948,18,(.group 6 1538 false)⟩)
(.leaf ⟨152966,18,(.group 6 1539 false)⟩))
(.branch 153002
(.leaf ⟨152984,18,(.group 6 1540 false)⟩)
(.leaf ⟨153002,18,(.group 6 1541 false)⟩))))
(.branch 153092
(.branch 153056
(.branch 153038
(.leaf ⟨153020,18,(.group 6 1542 false)⟩)
(.leaf ⟨153038,18,(.group 6 1543 false)⟩))
(.branch 153074
(.leaf ⟨153056,18,(.group 6 1544 false)⟩)
(.leaf ⟨153074,18,(.group 6 1545 false)⟩)))
(.branch 153128
(.branch 153110
(.leaf ⟨153092,18,(.group 6 1546 false)⟩)
(.leaf ⟨153110,18,(.group 6 1547 false)⟩))
(.branch 153146
(.leaf ⟨153128,18,(.group 6 1548 false)⟩)
(.leaf ⟨153146,18,(.group 6 1549 false)⟩)))))
(.branch 153308
(.branch 153236
(.branch 153200
(.branch 153182
(.leaf ⟨153164,18,(.group 6 1550 false)⟩)
(.leaf ⟨153182,18,(.group 6 1551 false)⟩))
(.branch 153218
(.leaf ⟨153200,18,(.group 6 1552 false)⟩)
(.leaf ⟨153218,18,(.group 6 1553 false)⟩)))
(.branch 153272
(.branch 153254
(.leaf ⟨153236,18,(.group 6 1554 false)⟩)
(.leaf ⟨153254,18,(.group 6 1555 false)⟩))
(.branch 153290
(.leaf ⟨153272,18,(.group 6 1556 false)⟩)
(.leaf ⟨153290,18,(.group 6 1557 false)⟩))))
(.branch 153380
(.branch 153344
(.branch 153326
(.leaf ⟨153308,18,(.group 6 1558 false)⟩)
(.leaf ⟨153326,18,(.group 6 1559 false)⟩))
(.branch 153362
(.leaf ⟨153344,18,(.group 6 1560 false)⟩)
(.leaf ⟨153362,18,(.group 6 1561 false)⟩)))
(.branch 153416
(.branch 153398
(.leaf ⟨153380,18,(.group 6 1562 false)⟩)
(.leaf ⟨153398,18,(.group 6 1563 false)⟩))
(.branch 153434
(.leaf ⟨153416,18,(.group 6 1564 false)⟩)
(.leaf ⟨153434,18,(.group 6 1565 false)⟩))))))
(.branch 153740
(.branch 153596
(.branch 153524
(.branch 153488
(.branch 153470
(.leaf ⟨153452,18,(.group 6 1566 false)⟩)
(.leaf ⟨153470,18,(.group 6 1567 false)⟩))
(.branch 153506
(.leaf ⟨153488,18,(.group 6 1568 false)⟩)
(.leaf ⟨153506,18,(.group 6 1569 false)⟩)))
(.branch 153560
(.branch 153542
(.leaf ⟨153524,18,(.group 6 1570 false)⟩)
(.leaf ⟨153542,18,(.group 6 1571 false)⟩))
(.branch 153578
(.leaf ⟨153560,18,(.group 6 1572 false)⟩)
(.leaf ⟨153578,18,(.group 6 1573 false)⟩))))
(.branch 153668
(.branch 153632
(.branch 153614
(.leaf ⟨153596,18,(.group 6 1574 false)⟩)
(.leaf ⟨153614,18,(.group 6 1575 false)⟩))
(.branch 153650
(.leaf ⟨153632,18,(.group 6 1576 false)⟩)
(.leaf ⟨153650,18,(.group 6 1577 false)⟩)))
(.branch 153704
(.branch 153686
(.leaf ⟨153668,18,(.group 6 1578 false)⟩)
(.leaf ⟨153686,18,(.group 6 1579 false)⟩))
(.branch 153722
(.leaf ⟨153704,18,(.group 6 1580 false)⟩)
(.leaf ⟨153722,18,(.group 6 1581 false)⟩)))))
(.branch 153884
(.branch 153812
(.branch 153776
(.branch 153758
(.leaf ⟨153740,18,(.group 6 1582 false)⟩)
(.leaf ⟨153758,18,(.group 6 1583 false)⟩))
(.branch 153794
(.leaf ⟨153776,18,(.group 6 1584 false)⟩)
(.leaf ⟨153794,18,(.group 6 1585 false)⟩)))
(.branch 153848
(.branch 153830
(.leaf ⟨153812,18,(.group 6 1586 false)⟩)
(.leaf ⟨153830,18,(.group 6 1587 false)⟩))
(.branch 153866
(.leaf ⟨153848,18,(.group 6 1588 false)⟩)
(.leaf ⟨153866,18,(.group 6 1589 false)⟩))))
(.branch 153956
(.branch 153920
(.branch 153902
(.leaf ⟨153884,18,(.group 6 1590 false)⟩)
(.leaf ⟨153902,18,(.group 6 1591 false)⟩))
(.branch 153938
(.leaf ⟨153920,18,(.group 6 1592 false)⟩)
(.leaf ⟨153938,18,(.group 6 1593 false)⟩)))
(.branch 153992
(.branch 153974
(.leaf ⟨153956,18,(.group 6 1594 false)⟩)
(.leaf ⟨153974,18,(.group 6 1595 false)⟩))
(.branch 154010
(.leaf ⟨153992,18,(.group 6 1596 false)⟩)
(.leaf ⟨154010,18,(.group 6 1597 false)⟩)))))))

theorem tree151_checked : tree151.check 152876 154028 = true := by decide +kernel

def tree152 : Tree := (.branch 154604
(.branch 154316
(.branch 154172
(.branch 154100
(.branch 154064
(.branch 154046
(.leaf ⟨154028,18,(.group 6 1598 false)⟩)
(.leaf ⟨154046,18,(.group 6 1599 false)⟩))
(.branch 154082
(.leaf ⟨154064,18,(.group 6 1600 false)⟩)
(.leaf ⟨154082,18,(.group 6 1601 false)⟩)))
(.branch 154136
(.branch 154118
(.leaf ⟨154100,18,(.group 6 1602 false)⟩)
(.leaf ⟨154118,18,(.group 6 1603 false)⟩))
(.branch 154154
(.leaf ⟨154136,18,(.group 6 1604 false)⟩)
(.leaf ⟨154154,18,(.group 6 1605 false)⟩))))
(.branch 154244
(.branch 154208
(.branch 154190
(.leaf ⟨154172,18,(.group 6 1606 false)⟩)
(.leaf ⟨154190,18,(.group 6 1607 false)⟩))
(.branch 154226
(.leaf ⟨154208,18,(.group 6 1608 false)⟩)
(.leaf ⟨154226,18,(.group 6 1609 false)⟩)))
(.branch 154280
(.branch 154262
(.leaf ⟨154244,18,(.group 6 1610 false)⟩)
(.leaf ⟨154262,18,(.group 6 1611 false)⟩))
(.branch 154298
(.leaf ⟨154280,18,(.group 6 1612 false)⟩)
(.leaf ⟨154298,18,(.group 6 1613 false)⟩)))))
(.branch 154460
(.branch 154388
(.branch 154352
(.branch 154334
(.leaf ⟨154316,18,(.group 6 1614 false)⟩)
(.leaf ⟨154334,18,(.group 6 1615 false)⟩))
(.branch 154370
(.leaf ⟨154352,18,(.group 6 1616 false)⟩)
(.leaf ⟨154370,18,(.group 6 1617 false)⟩)))
(.branch 154424
(.branch 154406
(.leaf ⟨154388,18,(.group 6 1618 false)⟩)
(.leaf ⟨154406,18,(.group 6 1619 false)⟩))
(.branch 154442
(.leaf ⟨154424,18,(.group 6 1620 false)⟩)
(.leaf ⟨154442,18,(.group 6 1621 false)⟩))))
(.branch 154532
(.branch 154496
(.branch 154478
(.leaf ⟨154460,18,(.group 6 1622 false)⟩)
(.leaf ⟨154478,18,(.group 6 1623 false)⟩))
(.branch 154514
(.leaf ⟨154496,18,(.group 6 1624 false)⟩)
(.leaf ⟨154514,18,(.group 6 1625 false)⟩)))
(.branch 154568
(.branch 154550
(.leaf ⟨154532,18,(.group 6 1626 false)⟩)
(.leaf ⟨154550,18,(.group 6 1627 false)⟩))
(.branch 154586
(.leaf ⟨154568,18,(.group 6 1628 false)⟩)
(.leaf ⟨154586,18,(.group 6 1629 false)⟩))))))
(.branch 154892
(.branch 154748
(.branch 154676
(.branch 154640
(.branch 154622
(.leaf ⟨154604,18,(.group 6 1630 false)⟩)
(.leaf ⟨154622,18,(.group 6 1631 false)⟩))
(.branch 154658
(.leaf ⟨154640,18,(.group 6 1632 false)⟩)
(.leaf ⟨154658,18,(.group 6 1633 false)⟩)))
(.branch 154712
(.branch 154694
(.leaf ⟨154676,18,(.group 6 1634 false)⟩)
(.leaf ⟨154694,18,(.group 6 1635 false)⟩))
(.branch 154730
(.leaf ⟨154712,18,(.group 6 1636 false)⟩)
(.leaf ⟨154730,18,(.group 6 1637 false)⟩))))
(.branch 154820
(.branch 154784
(.branch 154766
(.leaf ⟨154748,18,(.group 6 1638 false)⟩)
(.leaf ⟨154766,18,(.group 6 1639 false)⟩))
(.branch 154802
(.leaf ⟨154784,18,(.group 6 1640 false)⟩)
(.leaf ⟨154802,18,(.group 6 1641 false)⟩)))
(.branch 154856
(.branch 154838
(.leaf ⟨154820,18,(.group 6 1642 false)⟩)
(.leaf ⟨154838,18,(.group 6 1643 false)⟩))
(.branch 154874
(.leaf ⟨154856,18,(.group 6 1644 false)⟩)
(.leaf ⟨154874,18,(.group 6 1645 false)⟩)))))
(.branch 155036
(.branch 154964
(.branch 154928
(.branch 154910
(.leaf ⟨154892,18,(.group 6 1646 false)⟩)
(.leaf ⟨154910,18,(.group 6 1647 false)⟩))
(.branch 154946
(.leaf ⟨154928,18,(.group 6 1648 false)⟩)
(.leaf ⟨154946,18,(.group 6 1649 false)⟩)))
(.branch 155000
(.branch 154982
(.leaf ⟨154964,18,(.group 6 1650 false)⟩)
(.leaf ⟨154982,18,(.group 6 1651 false)⟩))
(.branch 155018
(.leaf ⟨155000,18,(.group 6 1652 false)⟩)
(.leaf ⟨155018,18,(.group 6 1653 false)⟩))))
(.branch 155108
(.branch 155072
(.branch 155054
(.leaf ⟨155036,18,(.group 6 1654 false)⟩)
(.leaf ⟨155054,18,(.group 6 1655 false)⟩))
(.branch 155090
(.leaf ⟨155072,18,(.group 6 1656 false)⟩)
(.leaf ⟨155090,18,(.group 6 1657 false)⟩)))
(.branch 155144
(.branch 155126
(.leaf ⟨155108,18,(.group 6 1658 false)⟩)
(.leaf ⟨155126,18,(.group 6 1659 false)⟩))
(.branch 155162
(.leaf ⟨155144,18,(.group 6 1660 false)⟩)
(.leaf ⟨155162,18,(.group 6 1661 false)⟩)))))))

theorem tree152_checked : tree152.check 154028 155180 = true := by decide +kernel

def tree153 : Tree := (.branch 155756
(.branch 155468
(.branch 155324
(.branch 155252
(.branch 155216
(.branch 155198
(.leaf ⟨155180,18,(.group 6 1662 false)⟩)
(.leaf ⟨155198,18,(.group 6 1663 false)⟩))
(.branch 155234
(.leaf ⟨155216,18,(.group 6 1664 false)⟩)
(.leaf ⟨155234,18,(.group 6 1665 false)⟩)))
(.branch 155288
(.branch 155270
(.leaf ⟨155252,18,(.group 6 1666 false)⟩)
(.leaf ⟨155270,18,(.group 6 1667 false)⟩))
(.branch 155306
(.leaf ⟨155288,18,(.group 6 1668 false)⟩)
(.leaf ⟨155306,18,(.group 6 1669 false)⟩))))
(.branch 155396
(.branch 155360
(.branch 155342
(.leaf ⟨155324,18,(.group 6 1670 false)⟩)
(.leaf ⟨155342,18,(.group 6 1671 false)⟩))
(.branch 155378
(.leaf ⟨155360,18,(.group 6 1672 false)⟩)
(.leaf ⟨155378,18,(.group 6 1673 false)⟩)))
(.branch 155432
(.branch 155414
(.leaf ⟨155396,18,(.group 6 1674 false)⟩)
(.leaf ⟨155414,18,(.group 6 1675 false)⟩))
(.branch 155450
(.leaf ⟨155432,18,(.group 6 1676 false)⟩)
(.leaf ⟨155450,18,(.group 6 1677 false)⟩)))))
(.branch 155612
(.branch 155540
(.branch 155504
(.branch 155486
(.leaf ⟨155468,18,(.group 6 1678 false)⟩)
(.leaf ⟨155486,18,(.group 6 1679 false)⟩))
(.branch 155522
(.leaf ⟨155504,18,(.group 6 1680 false)⟩)
(.leaf ⟨155522,18,(.group 6 1681 false)⟩)))
(.branch 155576
(.branch 155558
(.leaf ⟨155540,18,(.group 6 1682 false)⟩)
(.leaf ⟨155558,18,(.group 6 1683 false)⟩))
(.branch 155594
(.leaf ⟨155576,18,(.group 6 1684 false)⟩)
(.leaf ⟨155594,18,(.group 6 1685 false)⟩))))
(.branch 155684
(.branch 155648
(.branch 155630
(.leaf ⟨155612,18,(.group 6 1686 false)⟩)
(.leaf ⟨155630,18,(.group 6 1687 false)⟩))
(.branch 155666
(.leaf ⟨155648,18,(.group 6 1688 false)⟩)
(.leaf ⟨155666,18,(.group 6 1689 false)⟩)))
(.branch 155720
(.branch 155702
(.leaf ⟨155684,18,(.group 6 1690 false)⟩)
(.leaf ⟨155702,18,(.group 6 1691 false)⟩))
(.branch 155738
(.leaf ⟨155720,18,(.group 6 1692 false)⟩)
(.leaf ⟨155738,18,(.group 6 1693 false)⟩))))))
(.branch 156044
(.branch 155900
(.branch 155828
(.branch 155792
(.branch 155774
(.leaf ⟨155756,18,(.group 6 1694 false)⟩)
(.leaf ⟨155774,18,(.group 6 1695 false)⟩))
(.branch 155810
(.leaf ⟨155792,18,(.group 6 1696 false)⟩)
(.leaf ⟨155810,18,(.group 6 1697 false)⟩)))
(.branch 155864
(.branch 155846
(.leaf ⟨155828,18,(.group 6 1698 false)⟩)
(.leaf ⟨155846,18,(.group 6 1699 false)⟩))
(.branch 155882
(.leaf ⟨155864,18,(.group 6 1700 false)⟩)
(.leaf ⟨155882,18,(.group 6 1701 false)⟩))))
(.branch 155972
(.branch 155936
(.branch 155918
(.leaf ⟨155900,18,(.group 6 1702 false)⟩)
(.leaf ⟨155918,18,(.group 6 1703 false)⟩))
(.branch 155954
(.leaf ⟨155936,18,(.group 6 1704 false)⟩)
(.leaf ⟨155954,18,(.group 6 1705 false)⟩)))
(.branch 156008
(.branch 155990
(.leaf ⟨155972,18,(.group 6 1706 false)⟩)
(.leaf ⟨155990,18,(.group 6 1707 false)⟩))
(.branch 156026
(.leaf ⟨156008,18,(.group 6 1708 false)⟩)
(.leaf ⟨156026,18,(.group 6 1709 false)⟩)))))
(.branch 156188
(.branch 156116
(.branch 156080
(.branch 156062
(.leaf ⟨156044,18,(.group 6 1710 false)⟩)
(.leaf ⟨156062,18,(.group 6 1711 false)⟩))
(.branch 156098
(.leaf ⟨156080,18,(.group 6 1712 false)⟩)
(.leaf ⟨156098,18,(.group 6 1713 false)⟩)))
(.branch 156152
(.branch 156134
(.leaf ⟨156116,18,(.group 6 1714 false)⟩)
(.leaf ⟨156134,18,(.group 6 1715 false)⟩))
(.branch 156170
(.leaf ⟨156152,18,(.group 6 1716 false)⟩)
(.leaf ⟨156170,18,(.group 6 1717 false)⟩))))
(.branch 156260
(.branch 156224
(.branch 156206
(.leaf ⟨156188,18,(.group 6 1718 false)⟩)
(.leaf ⟨156206,18,(.group 6 1719 false)⟩))
(.branch 156242
(.leaf ⟨156224,18,(.group 6 1720 false)⟩)
(.leaf ⟨156242,18,(.group 6 1721 false)⟩)))
(.branch 156296
(.branch 156278
(.leaf ⟨156260,18,(.group 6 1722 false)⟩)
(.leaf ⟨156278,18,(.group 6 1723 false)⟩))
(.branch 156314
(.leaf ⟨156296,18,(.group 6 1724 false)⟩)
(.leaf ⟨156314,18,(.group 6 1725 false)⟩)))))))

theorem tree153_checked : tree153.check 155180 156332 = true := by decide +kernel

def tree154 : Tree := (.branch 156908
(.branch 156620
(.branch 156476
(.branch 156404
(.branch 156368
(.branch 156350
(.leaf ⟨156332,18,(.group 6 1726 false)⟩)
(.leaf ⟨156350,18,(.group 6 1727 false)⟩))
(.branch 156386
(.leaf ⟨156368,18,(.group 6 1728 false)⟩)
(.leaf ⟨156386,18,(.group 6 1729 false)⟩)))
(.branch 156440
(.branch 156422
(.leaf ⟨156404,18,(.group 6 1730 false)⟩)
(.leaf ⟨156422,18,(.group 6 1731 false)⟩))
(.branch 156458
(.leaf ⟨156440,18,(.group 6 1732 false)⟩)
(.leaf ⟨156458,18,(.group 6 1733 false)⟩))))
(.branch 156548
(.branch 156512
(.branch 156494
(.leaf ⟨156476,18,(.group 6 1734 false)⟩)
(.leaf ⟨156494,18,(.group 6 1735 false)⟩))
(.branch 156530
(.leaf ⟨156512,18,(.group 6 1736 false)⟩)
(.leaf ⟨156530,18,(.group 6 1737 false)⟩)))
(.branch 156584
(.branch 156566
(.leaf ⟨156548,18,(.group 6 1738 false)⟩)
(.leaf ⟨156566,18,(.group 6 1739 false)⟩))
(.branch 156602
(.leaf ⟨156584,18,(.group 6 1740 false)⟩)
(.leaf ⟨156602,18,(.group 6 1741 false)⟩)))))
(.branch 156764
(.branch 156692
(.branch 156656
(.branch 156638
(.leaf ⟨156620,18,(.group 6 1742 false)⟩)
(.leaf ⟨156638,18,(.group 6 1743 false)⟩))
(.branch 156674
(.leaf ⟨156656,18,(.group 7 319 false)⟩)
(.leaf ⟨156674,18,(.group 7 320 false)⟩)))
(.branch 156728
(.branch 156710
(.leaf ⟨156692,18,(.group 7 321 false)⟩)
(.leaf ⟨156710,18,(.group 7 322 false)⟩))
(.branch 156746
(.leaf ⟨156728,18,(.group 7 323 false)⟩)
(.leaf ⟨156746,18,(.group 7 324 false)⟩))))
(.branch 156836
(.branch 156800
(.branch 156782
(.leaf ⟨156764,18,(.group 7 325 false)⟩)
(.leaf ⟨156782,18,(.group 7 326 false)⟩))
(.branch 156818
(.leaf ⟨156800,18,(.group 7 327 false)⟩)
(.leaf ⟨156818,18,(.group 7 328 false)⟩)))
(.branch 156872
(.branch 156854
(.leaf ⟨156836,18,(.group 7 329 false)⟩)
(.leaf ⟨156854,18,(.group 7 330 false)⟩))
(.branch 156890
(.leaf ⟨156872,18,(.group 7 331 false)⟩)
(.leaf ⟨156890,18,(.group 7 332 false)⟩))))))
(.branch 157196
(.branch 157052
(.branch 156980
(.branch 156944
(.branch 156926
(.leaf ⟨156908,18,(.group 7 333 false)⟩)
(.leaf ⟨156926,18,(.group 7 334 false)⟩))
(.branch 156962
(.leaf ⟨156944,18,(.group 7 335 false)⟩)
(.leaf ⟨156962,18,(.group 7 336 false)⟩)))
(.branch 157016
(.branch 156998
(.leaf ⟨156980,18,(.group 7 337 false)⟩)
(.leaf ⟨156998,18,(.group 7 338 false)⟩))
(.branch 157034
(.leaf ⟨157016,18,(.group 7 339 false)⟩)
(.leaf ⟨157034,18,(.group 7 340 false)⟩))))
(.branch 157124
(.branch 157088
(.branch 157070
(.leaf ⟨157052,18,(.group 7 341 false)⟩)
(.leaf ⟨157070,18,(.group 7 342 false)⟩))
(.branch 157106
(.leaf ⟨157088,18,(.group 7 343 false)⟩)
(.leaf ⟨157106,18,(.group 7 344 false)⟩)))
(.branch 157160
(.branch 157142
(.leaf ⟨157124,18,(.group 7 345 false)⟩)
(.leaf ⟨157142,18,(.group 7 346 false)⟩))
(.branch 157178
(.leaf ⟨157160,18,(.group 7 347 false)⟩)
(.leaf ⟨157178,18,(.group 7 348 false)⟩)))))
(.branch 157340
(.branch 157268
(.branch 157232
(.branch 157214
(.leaf ⟨157196,18,(.group 7 349 false)⟩)
(.leaf ⟨157214,18,(.group 7 350 false)⟩))
(.branch 157250
(.leaf ⟨157232,18,(.group 7 351 false)⟩)
(.leaf ⟨157250,18,(.group 7 352 false)⟩)))
(.branch 157304
(.branch 157286
(.leaf ⟨157268,18,(.group 7 353 false)⟩)
(.leaf ⟨157286,18,(.group 7 354 false)⟩))
(.branch 157322
(.leaf ⟨157304,18,(.group 7 355 false)⟩)
(.leaf ⟨157322,18,(.group 7 356 false)⟩))))
(.branch 157412
(.branch 157376
(.branch 157358
(.leaf ⟨157340,18,(.group 7 357 false)⟩)
(.leaf ⟨157358,18,(.group 7 358 false)⟩))
(.branch 157394
(.leaf ⟨157376,18,(.group 7 359 false)⟩)
(.leaf ⟨157394,18,(.group 7 360 false)⟩)))
(.branch 157448
(.branch 157430
(.leaf ⟨157412,18,(.group 7 361 false)⟩)
(.leaf ⟨157430,18,(.group 7 362 false)⟩))
(.branch 157466
(.leaf ⟨157448,18,(.group 7 363 false)⟩)
(.leaf ⟨157466,18,(.group 7 364 false)⟩)))))))

theorem tree154_checked : tree154.check 156332 157484 = true := by decide +kernel

def tree155 : Tree := (.branch 158060
(.branch 157772
(.branch 157628
(.branch 157556
(.branch 157520
(.branch 157502
(.leaf ⟨157484,18,(.group 7 365 false)⟩)
(.leaf ⟨157502,18,(.group 7 366 false)⟩))
(.branch 157538
(.leaf ⟨157520,18,(.group 7 367 false)⟩)
(.leaf ⟨157538,18,(.group 7 368 false)⟩)))
(.branch 157592
(.branch 157574
(.leaf ⟨157556,18,(.group 7 369 false)⟩)
(.leaf ⟨157574,18,(.group 7 370 false)⟩))
(.branch 157610
(.leaf ⟨157592,18,(.group 7 371 false)⟩)
(.leaf ⟨157610,18,(.group 7 372 false)⟩))))
(.branch 157700
(.branch 157664
(.branch 157646
(.leaf ⟨157628,18,(.group 7 373 false)⟩)
(.leaf ⟨157646,18,(.group 7 374 false)⟩))
(.branch 157682
(.leaf ⟨157664,18,(.group 7 375 false)⟩)
(.leaf ⟨157682,18,(.group 7 376 false)⟩)))
(.branch 157736
(.branch 157718
(.leaf ⟨157700,18,(.group 7 377 false)⟩)
(.leaf ⟨157718,18,(.group 7 378 false)⟩))
(.branch 157754
(.leaf ⟨157736,18,(.group 7 379 false)⟩)
(.leaf ⟨157754,18,(.group 7 380 false)⟩)))))
(.branch 157916
(.branch 157844
(.branch 157808
(.branch 157790
(.leaf ⟨157772,18,(.group 7 381 false)⟩)
(.leaf ⟨157790,18,(.group 7 382 false)⟩))
(.branch 157826
(.leaf ⟨157808,18,(.group 7 383 false)⟩)
(.leaf ⟨157826,18,(.group 7 384 false)⟩)))
(.branch 157880
(.branch 157862
(.leaf ⟨157844,18,(.group 7 385 false)⟩)
(.leaf ⟨157862,18,(.group 7 386 false)⟩))
(.branch 157898
(.leaf ⟨157880,18,(.group 7 387 false)⟩)
(.leaf ⟨157898,18,(.group 7 388 false)⟩))))
(.branch 157988
(.branch 157952
(.branch 157934
(.leaf ⟨157916,18,(.group 7 389 false)⟩)
(.leaf ⟨157934,18,(.group 7 390 false)⟩))
(.branch 157970
(.leaf ⟨157952,18,(.group 7 391 false)⟩)
(.leaf ⟨157970,18,(.group 7 392 false)⟩)))
(.branch 158024
(.branch 158006
(.leaf ⟨157988,18,(.group 7 393 false)⟩)
(.leaf ⟨158006,18,(.group 7 394 false)⟩))
(.branch 158042
(.leaf ⟨158024,18,(.group 7 395 false)⟩)
(.leaf ⟨158042,18,(.group 7 396 false)⟩))))))
(.branch 158348
(.branch 158204
(.branch 158132
(.branch 158096
(.branch 158078
(.leaf ⟨158060,18,(.group 8 404 false)⟩)
(.leaf ⟨158078,18,(.group 8 405 false)⟩))
(.branch 158114
(.leaf ⟨158096,18,(.group 8 406 false)⟩)
(.leaf ⟨158114,18,(.group 8 407 false)⟩)))
(.branch 158168
(.branch 158150
(.leaf ⟨158132,18,(.group 8 408 false)⟩)
(.leaf ⟨158150,18,(.group 8 409 false)⟩))
(.branch 158186
(.leaf ⟨158168,18,(.group 8 410 false)⟩)
(.leaf ⟨158186,18,(.group 8 411 false)⟩))))
(.branch 158276
(.branch 158240
(.branch 158222
(.leaf ⟨158204,18,(.group 8 412 false)⟩)
(.leaf ⟨158222,18,(.group 8 413 false)⟩))
(.branch 158258
(.leaf ⟨158240,18,(.group 8 414 false)⟩)
(.leaf ⟨158258,18,(.group 8 415 false)⟩)))
(.branch 158312
(.branch 158294
(.leaf ⟨158276,18,(.group 8 416 false)⟩)
(.leaf ⟨158294,18,(.group 8 417 false)⟩))
(.branch 158330
(.leaf ⟨158312,18,(.group 8 418 false)⟩)
(.leaf ⟨158330,18,(.group 8 419 false)⟩)))))
(.branch 158492
(.branch 158420
(.branch 158384
(.branch 158366
(.leaf ⟨158348,18,(.group 8 420 false)⟩)
(.leaf ⟨158366,18,(.group 8 421 false)⟩))
(.branch 158402
(.leaf ⟨158384,18,(.group 8 422 false)⟩)
(.leaf ⟨158402,18,(.group 8 423 false)⟩)))
(.branch 158456
(.branch 158438
(.leaf ⟨158420,18,(.group 8 424 false)⟩)
(.leaf ⟨158438,18,(.group 8 425 false)⟩))
(.branch 158474
(.leaf ⟨158456,18,(.group 8 426 false)⟩)
(.leaf ⟨158474,18,(.group 8 427 false)⟩))))
(.branch 158564
(.branch 158528
(.branch 158510
(.leaf ⟨158492,18,(.group 8 428 false)⟩)
(.leaf ⟨158510,18,(.group 8 429 false)⟩))
(.branch 158546
(.leaf ⟨158528,18,(.group 8 430 false)⟩)
(.leaf ⟨158546,18,(.group 8 431 false)⟩)))
(.branch 158600
(.branch 158582
(.leaf ⟨158564,18,(.group 8 432 false)⟩)
(.leaf ⟨158582,18,(.group 8 433 false)⟩))
(.branch 158618
(.leaf ⟨158600,18,(.group 8 434 false)⟩)
(.leaf ⟨158618,18,(.group 8 435 false)⟩)))))))

theorem tree155_checked : tree155.check 157484 158636 = true := by decide +kernel

def tree156 : Tree := (.branch 159220
(.branch 158924
(.branch 158780
(.branch 158708
(.branch 158672
(.branch 158654
(.leaf ⟨158636,18,(.group 8 436 false)⟩)
(.leaf ⟨158654,18,(.group 8 437 false)⟩))
(.branch 158690
(.leaf ⟨158672,18,(.group 8 438 false)⟩)
(.leaf ⟨158690,18,(.group 8 439 false)⟩)))
(.branch 158744
(.branch 158726
(.leaf ⟨158708,18,(.group 8 440 false)⟩)
(.leaf ⟨158726,18,(.group 8 441 false)⟩))
(.branch 158762
(.leaf ⟨158744,18,(.group 8 442 false)⟩)
(.leaf ⟨158762,18,(.group 8 443 false)⟩))))
(.branch 158852
(.branch 158816
(.branch 158798
(.leaf ⟨158780,18,(.group 8 444 false)⟩)
(.leaf ⟨158798,18,(.group 8 445 false)⟩))
(.branch 158834
(.leaf ⟨158816,18,(.group 8 446 false)⟩)
(.leaf ⟨158834,18,(.group 8 447 false)⟩)))
(.branch 158888
(.branch 158870
(.leaf ⟨158852,18,(.group 8 448 false)⟩)
(.leaf ⟨158870,18,(.group 8 449 false)⟩))
(.branch 158906
(.leaf ⟨158888,18,(.group 8 450 false)⟩)
(.leaf ⟨158906,18,(.group 8 451 false)⟩)))))
(.branch 159068
(.branch 158996
(.branch 158960
(.branch 158942
(.leaf ⟨158924,18,(.group 8 452 false)⟩)
(.leaf ⟨158942,18,(.group 8 453 false)⟩))
(.branch 158978
(.leaf ⟨158960,18,(.group 8 454 false)⟩)
(.leaf ⟨158978,18,(.group 8 455 false)⟩)))
(.branch 159032
(.branch 159014
(.leaf ⟨158996,18,(.group 8 456 false)⟩)
(.leaf ⟨159014,18,(.group 8 457 false)⟩))
(.branch 159050
(.leaf ⟨159032,18,(.group 8 458 false)⟩)
(.leaf ⟨159050,18,(.group 8 459 false)⟩))))
(.branch 159144
(.branch 159106
(.branch 159087
(.leaf ⟨159068,19,(.group 0 908 false)⟩)
(.leaf ⟨159087,19,(.group 0 909 false)⟩))
(.branch 159125
(.leaf ⟨159106,19,(.group 0 910 false)⟩)
(.leaf ⟨159125,19,(.group 0 911 false)⟩)))
(.branch 159182
(.branch 159163
(.leaf ⟨159144,19,(.group 0 912 false)⟩)
(.leaf ⟨159163,19,(.group 0 913 false)⟩))
(.branch 159201
(.leaf ⟨159182,19,(.group 0 914 false)⟩)
(.leaf ⟨159201,19,(.group 0 915 false)⟩))))))
(.branch 159524
(.branch 159372
(.branch 159296
(.branch 159258
(.branch 159239
(.leaf ⟨159220,19,(.group 0 916 false)⟩)
(.leaf ⟨159239,19,(.group 0 917 false)⟩))
(.branch 159277
(.leaf ⟨159258,19,(.group 0 918 false)⟩)
(.leaf ⟨159277,19,(.group 0 919 false)⟩)))
(.branch 159334
(.branch 159315
(.leaf ⟨159296,19,(.group 0 920 false)⟩)
(.leaf ⟨159315,19,(.group 0 921 false)⟩))
(.branch 159353
(.leaf ⟨159334,19,(.group 0 922 false)⟩)
(.leaf ⟨159353,19,(.group 0 923 false)⟩))))
(.branch 159448
(.branch 159410
(.branch 159391
(.leaf ⟨159372,19,(.group 0 924 false)⟩)
(.leaf ⟨159391,19,(.group 0 925 false)⟩))
(.branch 159429
(.leaf ⟨159410,19,(.group 0 926 false)⟩)
(.leaf ⟨159429,19,(.group 0 927 false)⟩)))
(.branch 159486
(.branch 159467
(.leaf ⟨159448,19,(.group 0 928 false)⟩)
(.leaf ⟨159467,19,(.group 0 929 false)⟩))
(.branch 159505
(.leaf ⟨159486,19,(.group 0 930 false)⟩)
(.leaf ⟨159505,19,(.group 0 931 false)⟩)))))
(.branch 159676
(.branch 159600
(.branch 159562
(.branch 159543
(.leaf ⟨159524,19,(.group 0 932 false)⟩)
(.leaf ⟨159543,19,(.group 0 933 false)⟩))
(.branch 159581
(.leaf ⟨159562,19,(.group 0 934 false)⟩)
(.leaf ⟨159581,19,(.group 0 935 false)⟩)))
(.branch 159638
(.branch 159619
(.leaf ⟨159600,19,(.group 0 936 false)⟩)
(.leaf ⟨159619,19,(.group 0 937 false)⟩))
(.branch 159657
(.leaf ⟨159638,19,(.group 0 938 false)⟩)
(.leaf ⟨159657,19,(.group 0 939 false)⟩))))
(.branch 159752
(.branch 159714
(.branch 159695
(.leaf ⟨159676,19,(.group 0 940 false)⟩)
(.leaf ⟨159695,19,(.group 0 941 false)⟩))
(.branch 159733
(.leaf ⟨159714,19,(.group 0 942 false)⟩)
(.leaf ⟨159733,19,(.group 0 943 false)⟩)))
(.branch 159790
(.branch 159771
(.leaf ⟨159752,19,(.group 0 944 false)⟩)
(.leaf ⟨159771,19,(.group 0 945 false)⟩))
(.branch 159809
(.leaf ⟨159790,19,(.group 0 946 false)⟩)
(.leaf ⟨159809,19,(.group 0 947 false)⟩)))))))

theorem tree156_checked : tree156.check 158636 159828 = true := by decide +kernel

def tree157 : Tree := (.branch 160436
(.branch 160132
(.branch 159980
(.branch 159904
(.branch 159866
(.branch 159847
(.leaf ⟨159828,19,(.group 0 948 false)⟩)
(.leaf ⟨159847,19,(.group 0 949 false)⟩))
(.branch 159885
(.leaf ⟨159866,19,(.group 0 950 false)⟩)
(.leaf ⟨159885,19,(.group 0 951 false)⟩)))
(.branch 159942
(.branch 159923
(.leaf ⟨159904,19,(.group 0 952 false)⟩)
(.leaf ⟨159923,19,(.group 0 953 false)⟩))
(.branch 159961
(.leaf ⟨159942,19,(.group 0 954 false)⟩)
(.leaf ⟨159961,19,(.group 0 955 false)⟩))))
(.branch 160056
(.branch 160018
(.branch 159999
(.leaf ⟨159980,19,(.group 0 956 false)⟩)
(.leaf ⟨159999,19,(.group 0 957 false)⟩))
(.branch 160037
(.leaf ⟨160018,19,(.group 0 958 false)⟩)
(.leaf ⟨160037,19,(.group 0 959 false)⟩)))
(.branch 160094
(.branch 160075
(.leaf ⟨160056,19,(.group 0 960 false)⟩)
(.leaf ⟨160075,19,(.group 0 961 false)⟩))
(.branch 160113
(.leaf ⟨160094,19,(.group 0 962 false)⟩)
(.leaf ⟨160113,19,(.group 0 963 false)⟩)))))
(.branch 160284
(.branch 160208
(.branch 160170
(.branch 160151
(.leaf ⟨160132,19,(.group 0 964 false)⟩)
(.leaf ⟨160151,19,(.group 0 965 false)⟩))
(.branch 160189
(.leaf ⟨160170,19,(.group 0 966 false)⟩)
(.leaf ⟨160189,19,(.group 0 967 false)⟩)))
(.branch 160246
(.branch 160227
(.leaf ⟨160208,19,(.group 0 968 false)⟩)
(.leaf ⟨160227,19,(.group 0 969 false)⟩))
(.branch 160265
(.leaf ⟨160246,19,(.group 0 970 false)⟩)
(.leaf ⟨160265,19,(.group 0 971 false)⟩))))
(.branch 160360
(.branch 160322
(.branch 160303
(.leaf ⟨160284,19,(.group 0 972 false)⟩)
(.leaf ⟨160303,19,(.group 0 973 false)⟩))
(.branch 160341
(.leaf ⟨160322,19,(.group 0 974 false)⟩)
(.leaf ⟨160341,19,(.group 0 975 false)⟩)))
(.branch 160398
(.branch 160379
(.leaf ⟨160360,19,(.group 0 976 false)⟩)
(.leaf ⟨160379,19,(.group 0 977 false)⟩))
(.branch 160417
(.leaf ⟨160398,19,(.group 0 978 false)⟩)
(.leaf ⟨160417,19,(.group 0 979 false)⟩))))))
(.branch 160740
(.branch 160588
(.branch 160512
(.branch 160474
(.branch 160455
(.leaf ⟨160436,19,(.group 0 980 false)⟩)
(.leaf ⟨160455,19,(.group 0 981 false)⟩))
(.branch 160493
(.leaf ⟨160474,19,(.group 0 982 false)⟩)
(.leaf ⟨160493,19,(.group 0 983 false)⟩)))
(.branch 160550
(.branch 160531
(.leaf ⟨160512,19,(.group 0 984 false)⟩)
(.leaf ⟨160531,19,(.group 0 985 false)⟩))
(.branch 160569
(.leaf ⟨160550,19,(.group 0 986 false)⟩)
(.leaf ⟨160569,19,(.group 0 987 false)⟩))))
(.branch 160664
(.branch 160626
(.branch 160607
(.leaf ⟨160588,19,(.group 0 988 false)⟩)
(.leaf ⟨160607,19,(.group 0 989 false)⟩))
(.branch 160645
(.leaf ⟨160626,19,(.group 0 990 false)⟩)
(.leaf ⟨160645,19,(.group 0 991 false)⟩)))
(.branch 160702
(.branch 160683
(.leaf ⟨160664,19,(.group 0 992 false)⟩)
(.leaf ⟨160683,19,(.group 0 993 false)⟩))
(.branch 160721
(.leaf ⟨160702,19,(.group 0 994 false)⟩)
(.leaf ⟨160721,19,(.group 0 995 false)⟩)))))
(.branch 160892
(.branch 160816
(.branch 160778
(.branch 160759
(.leaf ⟨160740,19,(.group 0 996 false)⟩)
(.leaf ⟨160759,19,(.group 0 997 false)⟩))
(.branch 160797
(.leaf ⟨160778,19,(.group 0 998 false)⟩)
(.leaf ⟨160797,19,(.group 0 999 false)⟩)))
(.branch 160854
(.branch 160835
(.leaf ⟨160816,19,(.group 0 1000 false)⟩)
(.leaf ⟨160835,19,(.group 0 1001 false)⟩))
(.branch 160873
(.leaf ⟨160854,19,(.group 0 1002 false)⟩)
(.leaf ⟨160873,19,(.group 0 1003 false)⟩))))
(.branch 160968
(.branch 160930
(.branch 160911
(.leaf ⟨160892,19,(.group 0 1004 false)⟩)
(.leaf ⟨160911,19,(.group 0 1005 false)⟩))
(.branch 160949
(.leaf ⟨160930,19,(.group 0 1006 false)⟩)
(.leaf ⟨160949,19,(.group 0 1007 false)⟩)))
(.branch 161006
(.branch 160987
(.leaf ⟨160968,19,(.group 0 1008 false)⟩)
(.leaf ⟨160987,19,(.group 0 1009 false)⟩))
(.branch 161025
(.leaf ⟨161006,19,(.group 0 1010 false)⟩)
(.leaf ⟨161025,19,(.group 0 1011 false)⟩)))))))

theorem tree157_checked : tree157.check 159828 161044 = true := by decide +kernel

def tree158 : Tree := (.branch 161652
(.branch 161348
(.branch 161196
(.branch 161120
(.branch 161082
(.branch 161063
(.leaf ⟨161044,19,(.group 0 1012 false)⟩)
(.leaf ⟨161063,19,(.group 0 1013 false)⟩))
(.branch 161101
(.leaf ⟨161082,19,(.group 0 1014 false)⟩)
(.leaf ⟨161101,19,(.group 0 1015 false)⟩)))
(.branch 161158
(.branch 161139
(.leaf ⟨161120,19,(.group 0 1016 false)⟩)
(.leaf ⟨161139,19,(.group 0 1017 false)⟩))
(.branch 161177
(.leaf ⟨161158,19,(.group 0 1018 false)⟩)
(.leaf ⟨161177,19,(.group 0 1019 false)⟩))))
(.branch 161272
(.branch 161234
(.branch 161215
(.leaf ⟨161196,19,(.group 0 1020 false)⟩)
(.leaf ⟨161215,19,(.group 0 1021 false)⟩))
(.branch 161253
(.leaf ⟨161234,19,(.group 0 1022 false)⟩)
(.leaf ⟨161253,19,(.group 0 1023 false)⟩)))
(.branch 161310
(.branch 161291
(.leaf ⟨161272,19,(.group 1 364 false)⟩)
(.leaf ⟨161291,19,(.group 1 365 false)⟩))
(.branch 161329
(.leaf ⟨161310,19,(.group 1 366 false)⟩)
(.leaf ⟨161329,19,(.group 1 367 false)⟩)))))
(.branch 161500
(.branch 161424
(.branch 161386
(.branch 161367
(.leaf ⟨161348,19,(.group 1 368 false)⟩)
(.leaf ⟨161367,19,(.group 1 369 false)⟩))
(.branch 161405
(.leaf ⟨161386,19,(.group 1 370 false)⟩)
(.leaf ⟨161405,19,(.group 1 371 false)⟩)))
(.branch 161462
(.branch 161443
(.leaf ⟨161424,19,(.group 1 372 false)⟩)
(.leaf ⟨161443,19,(.group 1 373 false)⟩))
(.branch 161481
(.leaf ⟨161462,19,(.group 1 374 false)⟩)
(.leaf ⟨161481,19,(.group 1 375 false)⟩))))
(.branch 161576
(.branch 161538
(.branch 161519
(.leaf ⟨161500,19,(.group 1 376 false)⟩)
(.leaf ⟨161519,19,(.group 1 377 false)⟩))
(.branch 161557
(.leaf ⟨161538,19,(.group 1 378 false)⟩)
(.leaf ⟨161557,19,(.group 1 379 false)⟩)))
(.branch 161614
(.branch 161595
(.leaf ⟨161576,19,(.group 1 380 false)⟩)
(.leaf ⟨161595,19,(.group 1 381 false)⟩))
(.branch 161633
(.leaf ⟨161614,19,(.group 1 382 false)⟩)
(.leaf ⟨161633,19,(.group 1 383 false)⟩))))))
(.branch 161956
(.branch 161804
(.branch 161728
(.branch 161690
(.branch 161671
(.leaf ⟨161652,19,(.group 1 384 false)⟩)
(.leaf ⟨161671,19,(.group 1 385 false)⟩))
(.branch 161709
(.leaf ⟨161690,19,(.group 1 386 false)⟩)
(.leaf ⟨161709,19,(.group 1 387 false)⟩)))
(.branch 161766
(.branch 161747
(.leaf ⟨161728,19,(.group 1 388 false)⟩)
(.leaf ⟨161747,19,(.group 1 389 false)⟩))
(.branch 161785
(.leaf ⟨161766,19,(.group 1 390 false)⟩)
(.leaf ⟨161785,19,(.group 1 391 false)⟩))))
(.branch 161880
(.branch 161842
(.branch 161823
(.leaf ⟨161804,19,(.group 1 392 false)⟩)
(.leaf ⟨161823,19,(.group 1 393 false)⟩))
(.branch 161861
(.leaf ⟨161842,19,(.group 1 394 false)⟩)
(.leaf ⟨161861,19,(.group 1 395 false)⟩)))
(.branch 161918
(.branch 161899
(.leaf ⟨161880,19,(.group 1 396 false)⟩)
(.leaf ⟨161899,19,(.group 1 397 false)⟩))
(.branch 161937
(.leaf ⟨161918,19,(.group 1 398 false)⟩)
(.leaf ⟨161937,19,(.group 1 399 false)⟩)))))
(.branch 162108
(.branch 162032
(.branch 161994
(.branch 161975
(.leaf ⟨161956,19,(.group 1 400 false)⟩)
(.leaf ⟨161975,19,(.group 1 401 false)⟩))
(.branch 162013
(.leaf ⟨161994,19,(.group 1 402 false)⟩)
(.leaf ⟨162013,19,(.group 1 403 false)⟩)))
(.branch 162070
(.branch 162051
(.leaf ⟨162032,19,(.group 1 404 false)⟩)
(.leaf ⟨162051,19,(.group 1 405 false)⟩))
(.branch 162089
(.leaf ⟨162070,19,(.group 1 406 false)⟩)
(.leaf ⟨162089,19,(.group 1 407 false)⟩))))
(.branch 162184
(.branch 162146
(.branch 162127
(.leaf ⟨162108,19,(.group 1 408 false)⟩)
(.leaf ⟨162127,19,(.group 1 409 false)⟩))
(.branch 162165
(.leaf ⟨162146,19,(.group 1 410 false)⟩)
(.leaf ⟨162165,19,(.group 1 411 false)⟩)))
(.branch 162222
(.branch 162203
(.leaf ⟨162184,19,(.group 1 412 false)⟩)
(.leaf ⟨162203,19,(.group 1 413 false)⟩))
(.branch 162241
(.leaf ⟨162222,19,(.group 1 414 false)⟩)
(.leaf ⟨162241,19,(.group 1 415 false)⟩)))))))

theorem tree158_checked : tree158.check 161044 162260 = true := by decide +kernel

def tree159 : Tree := (.branch 162868
(.branch 162564
(.branch 162412
(.branch 162336
(.branch 162298
(.branch 162279
(.leaf ⟨162260,19,(.group 1 416 false)⟩)
(.leaf ⟨162279,19,(.group 1 417 false)⟩))
(.branch 162317
(.leaf ⟨162298,19,(.group 1 418 false)⟩)
(.leaf ⟨162317,19,(.group 1 419 false)⟩)))
(.branch 162374
(.branch 162355
(.leaf ⟨162336,19,(.group 1 420 false)⟩)
(.leaf ⟨162355,19,(.group 1 421 false)⟩))
(.branch 162393
(.leaf ⟨162374,19,(.group 1 422 false)⟩)
(.leaf ⟨162393,19,(.group 1 423 false)⟩))))
(.branch 162488
(.branch 162450
(.branch 162431
(.leaf ⟨162412,19,(.group 1 424 false)⟩)
(.leaf ⟨162431,19,(.group 1 425 false)⟩))
(.branch 162469
(.leaf ⟨162450,19,(.group 1 426 false)⟩)
(.leaf ⟨162469,19,(.group 1 427 false)⟩)))
(.branch 162526
(.branch 162507
(.leaf ⟨162488,19,(.group 1 428 false)⟩)
(.leaf ⟨162507,19,(.group 1 429 false)⟩))
(.branch 162545
(.leaf ⟨162526,19,(.group 1 430 false)⟩)
(.leaf ⟨162545,19,(.group 1 431 false)⟩)))))
(.branch 162716
(.branch 162640
(.branch 162602
(.branch 162583
(.leaf ⟨162564,19,(.group 1 432 false)⟩)
(.leaf ⟨162583,19,(.group 1 433 false)⟩))
(.branch 162621
(.leaf ⟨162602,19,(.group 1 434 false)⟩)
(.leaf ⟨162621,19,(.group 1 435 false)⟩)))
(.branch 162678
(.branch 162659
(.leaf ⟨162640,19,(.group 1 436 false)⟩)
(.leaf ⟨162659,19,(.group 1 437 false)⟩))
(.branch 162697
(.leaf ⟨162678,19,(.group 1 438 false)⟩)
(.leaf ⟨162697,19,(.group 1 439 false)⟩))))
(.branch 162792
(.branch 162754
(.branch 162735
(.leaf ⟨162716,19,(.group 1 440 false)⟩)
(.leaf ⟨162735,19,(.group 1 441 false)⟩))
(.branch 162773
(.leaf ⟨162754,19,(.group 1 442 false)⟩)
(.leaf ⟨162773,19,(.group 1 443 false)⟩)))
(.branch 162830
(.branch 162811
(.leaf ⟨162792,19,(.group 1 444 false)⟩)
(.leaf ⟨162811,19,(.group 1 445 false)⟩))
(.branch 162849
(.leaf ⟨162830,19,(.group 1 446 false)⟩)
(.leaf ⟨162849,19,(.group 1 447 false)⟩))))))
(.branch 163172
(.branch 163020
(.branch 162944
(.branch 162906
(.branch 162887
(.leaf ⟨162868,19,(.group 1 448 false)⟩)
(.leaf ⟨162887,19,(.group 1 449 false)⟩))
(.branch 162925
(.leaf ⟨162906,19,(.group 1 450 false)⟩)
(.leaf ⟨162925,19,(.group 1 451 false)⟩)))
(.branch 162982
(.branch 162963
(.leaf ⟨162944,19,(.group 1 452 false)⟩)
(.leaf ⟨162963,19,(.group 1 453 false)⟩))
(.branch 163001
(.leaf ⟨162982,19,(.group 1 454 false)⟩)
(.leaf ⟨163001,19,(.group 2 364 false)⟩))))
(.branch 163096
(.branch 163058
(.branch 163039
(.leaf ⟨163020,19,(.group 2 365 false)⟩)
(.leaf ⟨163039,19,(.group 2 366 false)⟩))
(.branch 163077
(.leaf ⟨163058,19,(.group 2 367 false)⟩)
(.leaf ⟨163077,19,(.group 2 368 false)⟩)))
(.branch 163134
(.branch 163115
(.leaf ⟨163096,19,(.group 2 369 false)⟩)
(.leaf ⟨163115,19,(.group 2 370 false)⟩))
(.branch 163153
(.leaf ⟨163134,19,(.group 2 371 false)⟩)
(.leaf ⟨163153,19,(.group 2 372 false)⟩)))))
(.branch 163324
(.branch 163248
(.branch 163210
(.branch 163191
(.leaf ⟨163172,19,(.group 2 373 false)⟩)
(.leaf ⟨163191,19,(.group 2 374 false)⟩))
(.branch 163229
(.leaf ⟨163210,19,(.group 2 375 false)⟩)
(.leaf ⟨163229,19,(.group 2 376 false)⟩)))
(.branch 163286
(.branch 163267
(.leaf ⟨163248,19,(.group 2 377 false)⟩)
(.leaf ⟨163267,19,(.group 2 378 false)⟩))
(.branch 163305
(.leaf ⟨163286,19,(.group 2 379 false)⟩)
(.leaf ⟨163305,19,(.group 2 380 false)⟩))))
(.branch 163400
(.branch 163362
(.branch 163343
(.leaf ⟨163324,19,(.group 2 381 false)⟩)
(.leaf ⟨163343,19,(.group 2 382 false)⟩))
(.branch 163381
(.leaf ⟨163362,19,(.group 2 383 false)⟩)
(.leaf ⟨163381,19,(.group 2 384 false)⟩)))
(.branch 163438
(.branch 163419
(.leaf ⟨163400,19,(.group 2 385 false)⟩)
(.leaf ⟨163419,19,(.group 2 386 false)⟩))
(.branch 163457
(.leaf ⟨163438,19,(.group 2 387 false)⟩)
(.leaf ⟨163457,19,(.group 2 388 false)⟩)))))))

theorem tree159_checked : tree159.check 162260 163476 = true := by decide +kernel

def tree160 : Tree := (.branch 164084
(.branch 163780
(.branch 163628
(.branch 163552
(.branch 163514
(.branch 163495
(.leaf ⟨163476,19,(.group 2 389 false)⟩)
(.leaf ⟨163495,19,(.group 2 390 false)⟩))
(.branch 163533
(.leaf ⟨163514,19,(.group 2 391 false)⟩)
(.leaf ⟨163533,19,(.group 2 392 false)⟩)))
(.branch 163590
(.branch 163571
(.leaf ⟨163552,19,(.group 2 393 false)⟩)
(.leaf ⟨163571,19,(.group 2 394 false)⟩))
(.branch 163609
(.leaf ⟨163590,19,(.group 2 395 false)⟩)
(.leaf ⟨163609,19,(.group 2 396 false)⟩))))
(.branch 163704
(.branch 163666
(.branch 163647
(.leaf ⟨163628,19,(.group 2 397 false)⟩)
(.leaf ⟨163647,19,(.group 2 398 false)⟩))
(.branch 163685
(.leaf ⟨163666,19,(.group 2 399 false)⟩)
(.leaf ⟨163685,19,(.group 2 400 false)⟩)))
(.branch 163742
(.branch 163723
(.leaf ⟨163704,19,(.group 2 401 false)⟩)
(.leaf ⟨163723,19,(.group 2 402 false)⟩))
(.branch 163761
(.leaf ⟨163742,19,(.group 2 403 false)⟩)
(.leaf ⟨163761,19,(.group 2 404 false)⟩)))))
(.branch 163932
(.branch 163856
(.branch 163818
(.branch 163799
(.leaf ⟨163780,19,(.group 2 405 false)⟩)
(.leaf ⟨163799,19,(.group 2 406 false)⟩))
(.branch 163837
(.leaf ⟨163818,19,(.group 2 407 false)⟩)
(.leaf ⟨163837,19,(.group 2 408 false)⟩)))
(.branch 163894
(.branch 163875
(.leaf ⟨163856,19,(.group 2 409 false)⟩)
(.leaf ⟨163875,19,(.group 2 410 false)⟩))
(.branch 163913
(.leaf ⟨163894,19,(.group 2 411 false)⟩)
(.leaf ⟨163913,19,(.group 2 412 false)⟩))))
(.branch 164008
(.branch 163970
(.branch 163951
(.leaf ⟨163932,19,(.group 2 413 false)⟩)
(.leaf ⟨163951,19,(.group 2 414 false)⟩))
(.branch 163989
(.leaf ⟨163970,19,(.group 2 415 false)⟩)
(.leaf ⟨163989,19,(.group 2 416 false)⟩)))
(.branch 164046
(.branch 164027
(.leaf ⟨164008,19,(.group 2 417 false)⟩)
(.leaf ⟨164027,19,(.group 2 418 false)⟩))
(.branch 164065
(.leaf ⟨164046,19,(.group 2 419 false)⟩)
(.leaf ⟨164065,19,(.group 2 420 false)⟩))))))
(.branch 164388
(.branch 164236
(.branch 164160
(.branch 164122
(.branch 164103
(.leaf ⟨164084,19,(.group 2 421 false)⟩)
(.leaf ⟨164103,19,(.group 2 422 false)⟩))
(.branch 164141
(.leaf ⟨164122,19,(.group 2 423 false)⟩)
(.leaf ⟨164141,19,(.group 2 424 false)⟩)))
(.branch 164198
(.branch 164179
(.leaf ⟨164160,19,(.group 2 425 false)⟩)
(.leaf ⟨164179,19,(.group 2 426 false)⟩))
(.branch 164217
(.leaf ⟨164198,19,(.group 2 427 false)⟩)
(.leaf ⟨164217,19,(.group 2 428 false)⟩))))
(.branch 164312
(.branch 164274
(.branch 164255
(.leaf ⟨164236,19,(.group 2 429 false)⟩)
(.leaf ⟨164255,19,(.group 2 430 false)⟩))
(.branch 164293
(.leaf ⟨164274,19,(.group 2 431 false)⟩)
(.leaf ⟨164293,19,(.group 2 432 false)⟩)))
(.branch 164350
(.branch 164331
(.leaf ⟨164312,19,(.group 2 433 false)⟩)
(.leaf ⟨164331,19,(.group 2 434 false)⟩))
(.branch 164369
(.leaf ⟨164350,19,(.group 2 435 false)⟩)
(.leaf ⟨164369,19,(.group 2 436 false)⟩)))))
(.branch 164540
(.branch 164464
(.branch 164426
(.branch 164407
(.leaf ⟨164388,19,(.group 2 437 false)⟩)
(.leaf ⟨164407,19,(.group 2 438 false)⟩))
(.branch 164445
(.leaf ⟨164426,19,(.group 2 439 false)⟩)
(.leaf ⟨164445,19,(.group 2 440 false)⟩)))
(.branch 164502
(.branch 164483
(.leaf ⟨164464,19,(.group 2 441 false)⟩)
(.leaf ⟨164483,19,(.group 2 442 false)⟩))
(.branch 164521
(.leaf ⟨164502,19,(.group 2 443 false)⟩)
(.leaf ⟨164521,19,(.group 2 444 false)⟩))))
(.branch 164616
(.branch 164578
(.branch 164559
(.leaf ⟨164540,19,(.group 2 445 false)⟩)
(.leaf ⟨164559,19,(.group 2 446 false)⟩))
(.branch 164597
(.leaf ⟨164578,19,(.group 2 447 false)⟩)
(.leaf ⟨164597,19,(.group 2 448 false)⟩)))
(.branch 164654
(.branch 164635
(.leaf ⟨164616,19,(.group 2 449 false)⟩)
(.leaf ⟨164635,19,(.group 2 450 false)⟩))
(.branch 164673
(.leaf ⟨164654,19,(.group 2 451 false)⟩)
(.leaf ⟨164673,19,(.group 2 452 false)⟩)))))))

theorem tree160_checked : tree160.check 163476 164692 = true := by decide +kernel

def tree161 : Tree := (.branch 165300
(.branch 164996
(.branch 164844
(.branch 164768
(.branch 164730
(.branch 164711
(.leaf ⟨164692,19,(.group 2 453 false)⟩)
(.leaf ⟨164711,19,(.group 2 454 false)⟩))
(.branch 164749
(.leaf ⟨164730,19,(.group 3 364 false)⟩)
(.leaf ⟨164749,19,(.group 3 365 false)⟩)))
(.branch 164806
(.branch 164787
(.leaf ⟨164768,19,(.group 3 366 false)⟩)
(.leaf ⟨164787,19,(.group 3 367 false)⟩))
(.branch 164825
(.leaf ⟨164806,19,(.group 3 368 false)⟩)
(.leaf ⟨164825,19,(.group 3 369 false)⟩))))
(.branch 164920
(.branch 164882
(.branch 164863
(.leaf ⟨164844,19,(.group 3 370 false)⟩)
(.leaf ⟨164863,19,(.group 3 371 false)⟩))
(.branch 164901
(.leaf ⟨164882,19,(.group 3 372 false)⟩)
(.leaf ⟨164901,19,(.group 3 373 false)⟩)))
(.branch 164958
(.branch 164939
(.leaf ⟨164920,19,(.group 3 374 false)⟩)
(.leaf ⟨164939,19,(.group 3 375 false)⟩))
(.branch 164977
(.leaf ⟨164958,19,(.group 3 376 false)⟩)
(.leaf ⟨164977,19,(.group 3 377 false)⟩)))))
(.branch 165148
(.branch 165072
(.branch 165034
(.branch 165015
(.leaf ⟨164996,19,(.group 3 378 false)⟩)
(.leaf ⟨165015,19,(.group 3 379 false)⟩))
(.branch 165053
(.leaf ⟨165034,19,(.group 3 380 false)⟩)
(.leaf ⟨165053,19,(.group 3 381 false)⟩)))
(.branch 165110
(.branch 165091
(.leaf ⟨165072,19,(.group 3 382 false)⟩)
(.leaf ⟨165091,19,(.group 3 383 false)⟩))
(.branch 165129
(.leaf ⟨165110,19,(.group 3 384 false)⟩)
(.leaf ⟨165129,19,(.group 3 385 false)⟩))))
(.branch 165224
(.branch 165186
(.branch 165167
(.leaf ⟨165148,19,(.group 3 386 false)⟩)
(.leaf ⟨165167,19,(.group 3 387 false)⟩))
(.branch 165205
(.leaf ⟨165186,19,(.group 3 388 false)⟩)
(.leaf ⟨165205,19,(.group 3 389 false)⟩)))
(.branch 165262
(.branch 165243
(.leaf ⟨165224,19,(.group 3 390 false)⟩)
(.leaf ⟨165243,19,(.group 3 391 false)⟩))
(.branch 165281
(.leaf ⟨165262,19,(.group 3 392 false)⟩)
(.leaf ⟨165281,19,(.group 3 393 false)⟩))))))
(.branch 165604
(.branch 165452
(.branch 165376
(.branch 165338
(.branch 165319
(.leaf ⟨165300,19,(.group 3 394 false)⟩)
(.leaf ⟨165319,19,(.group 3 395 false)⟩))
(.branch 165357
(.leaf ⟨165338,19,(.group 3 396 false)⟩)
(.leaf ⟨165357,19,(.group 3 397 false)⟩)))
(.branch 165414
(.branch 165395
(.leaf ⟨165376,19,(.group 3 398 false)⟩)
(.leaf ⟨165395,19,(.group 3 399 false)⟩))
(.branch 165433
(.leaf ⟨165414,19,(.group 3 400 false)⟩)
(.leaf ⟨165433,19,(.group 3 401 false)⟩))))
(.branch 165528
(.branch 165490
(.branch 165471
(.leaf ⟨165452,19,(.group 3 402 false)⟩)
(.leaf ⟨165471,19,(.group 3 403 false)⟩))
(.branch 165509
(.leaf ⟨165490,19,(.group 3 404 false)⟩)
(.leaf ⟨165509,19,(.group 3 405 false)⟩)))
(.branch 165566
(.branch 165547
(.leaf ⟨165528,19,(.group 3 406 false)⟩)
(.leaf ⟨165547,19,(.group 3 407 false)⟩))
(.branch 165585
(.leaf ⟨165566,19,(.group 3 408 false)⟩)
(.leaf ⟨165585,19,(.group 3 409 false)⟩)))))
(.branch 165756
(.branch 165680
(.branch 165642
(.branch 165623
(.leaf ⟨165604,19,(.group 3 410 false)⟩)
(.leaf ⟨165623,19,(.group 3 411 false)⟩))
(.branch 165661
(.leaf ⟨165642,19,(.group 3 412 false)⟩)
(.leaf ⟨165661,19,(.group 3 413 false)⟩)))
(.branch 165718
(.branch 165699
(.leaf ⟨165680,19,(.group 3 414 false)⟩)
(.leaf ⟨165699,19,(.group 3 415 false)⟩))
(.branch 165737
(.leaf ⟨165718,19,(.group 3 416 false)⟩)
(.leaf ⟨165737,19,(.group 3 417 false)⟩))))
(.branch 165832
(.branch 165794
(.branch 165775
(.leaf ⟨165756,19,(.group 3 418 false)⟩)
(.leaf ⟨165775,19,(.group 3 419 false)⟩))
(.branch 165813
(.leaf ⟨165794,19,(.group 3 420 false)⟩)
(.leaf ⟨165813,19,(.group 3 421 false)⟩)))
(.branch 165870
(.branch 165851
(.leaf ⟨165832,19,(.group 3 422 false)⟩)
(.leaf ⟨165851,19,(.group 3 423 false)⟩))
(.branch 165889
(.leaf ⟨165870,19,(.group 3 424 false)⟩)
(.leaf ⟨165889,19,(.group 3 425 false)⟩)))))))

theorem tree161_checked : tree161.check 164692 165908 = true := by decide +kernel

def tree162 : Tree := (.branch 166516
(.branch 166212
(.branch 166060
(.branch 165984
(.branch 165946
(.branch 165927
(.leaf ⟨165908,19,(.group 3 426 false)⟩)
(.leaf ⟨165927,19,(.group 3 427 false)⟩))
(.branch 165965
(.leaf ⟨165946,19,(.group 3 428 false)⟩)
(.leaf ⟨165965,19,(.group 3 429 false)⟩)))
(.branch 166022
(.branch 166003
(.leaf ⟨165984,19,(.group 3 430 false)⟩)
(.leaf ⟨166003,19,(.group 3 431 false)⟩))
(.branch 166041
(.leaf ⟨166022,19,(.group 3 432 false)⟩)
(.leaf ⟨166041,19,(.group 3 433 false)⟩))))
(.branch 166136
(.branch 166098
(.branch 166079
(.leaf ⟨166060,19,(.group 3 434 false)⟩)
(.leaf ⟨166079,19,(.group 3 435 false)⟩))
(.branch 166117
(.leaf ⟨166098,19,(.group 3 436 false)⟩)
(.leaf ⟨166117,19,(.group 3 437 false)⟩)))
(.branch 166174
(.branch 166155
(.leaf ⟨166136,19,(.group 3 438 false)⟩)
(.leaf ⟨166155,19,(.group 3 439 false)⟩))
(.branch 166193
(.leaf ⟨166174,19,(.group 3 440 false)⟩)
(.leaf ⟨166193,19,(.group 3 441 false)⟩)))))
(.branch 166364
(.branch 166288
(.branch 166250
(.branch 166231
(.leaf ⟨166212,19,(.group 3 442 false)⟩)
(.leaf ⟨166231,19,(.group 3 443 false)⟩))
(.branch 166269
(.leaf ⟨166250,19,(.group 3 444 false)⟩)
(.leaf ⟨166269,19,(.group 3 445 false)⟩)))
(.branch 166326
(.branch 166307
(.leaf ⟨166288,19,(.group 3 446 false)⟩)
(.leaf ⟨166307,19,(.group 3 447 false)⟩))
(.branch 166345
(.leaf ⟨166326,19,(.group 3 448 false)⟩)
(.leaf ⟨166345,19,(.group 3 449 false)⟩))))
(.branch 166440
(.branch 166402
(.branch 166383
(.leaf ⟨166364,19,(.group 3 450 false)⟩)
(.leaf ⟨166383,19,(.group 3 451 false)⟩))
(.branch 166421
(.leaf ⟨166402,19,(.group 3 452 false)⟩)
(.leaf ⟨166421,19,(.group 3 453 false)⟩)))
(.branch 166478
(.branch 166459
(.leaf ⟨166440,19,(.group 3 454 false)⟩)
(.leaf ⟨166459,19,(.group 4 364 false)⟩))
(.branch 166497
(.leaf ⟨166478,19,(.group 4 365 false)⟩)
(.leaf ⟨166497,19,(.group 4 366 false)⟩))))))
(.branch 166820
(.branch 166668
(.branch 166592
(.branch 166554
(.branch 166535
(.leaf ⟨166516,19,(.group 4 367 false)⟩)
(.leaf ⟨166535,19,(.group 4 368 false)⟩))
(.branch 166573
(.leaf ⟨166554,19,(.group 4 369 false)⟩)
(.leaf ⟨166573,19,(.group 4 370 false)⟩)))
(.branch 166630
(.branch 166611
(.leaf ⟨166592,19,(.group 4 371 false)⟩)
(.leaf ⟨166611,19,(.group 4 372 false)⟩))
(.branch 166649
(.leaf ⟨166630,19,(.group 4 373 false)⟩)
(.leaf ⟨166649,19,(.group 4 374 false)⟩))))
(.branch 166744
(.branch 166706
(.branch 166687
(.leaf ⟨166668,19,(.group 4 375 false)⟩)
(.leaf ⟨166687,19,(.group 4 376 false)⟩))
(.branch 166725
(.leaf ⟨166706,19,(.group 4 377 false)⟩)
(.leaf ⟨166725,19,(.group 4 378 false)⟩)))
(.branch 166782
(.branch 166763
(.leaf ⟨166744,19,(.group 4 379 false)⟩)
(.leaf ⟨166763,19,(.group 4 380 false)⟩))
(.branch 166801
(.leaf ⟨166782,19,(.group 4 381 false)⟩)
(.leaf ⟨166801,19,(.group 4 382 false)⟩)))))
(.branch 166972
(.branch 166896
(.branch 166858
(.branch 166839
(.leaf ⟨166820,19,(.group 4 383 false)⟩)
(.leaf ⟨166839,19,(.group 4 384 false)⟩))
(.branch 166877
(.leaf ⟨166858,19,(.group 4 385 false)⟩)
(.leaf ⟨166877,19,(.group 4 386 false)⟩)))
(.branch 166934
(.branch 166915
(.leaf ⟨166896,19,(.group 4 387 false)⟩)
(.leaf ⟨166915,19,(.group 4 388 false)⟩))
(.branch 166953
(.leaf ⟨166934,19,(.group 4 389 false)⟩)
(.leaf ⟨166953,19,(.group 4 390 false)⟩))))
(.branch 167048
(.branch 167010
(.branch 166991
(.leaf ⟨166972,19,(.group 4 391 false)⟩)
(.leaf ⟨166991,19,(.group 4 392 false)⟩))
(.branch 167029
(.leaf ⟨167010,19,(.group 4 393 false)⟩)
(.leaf ⟨167029,19,(.group 4 394 false)⟩)))
(.branch 167086
(.branch 167067
(.leaf ⟨167048,19,(.group 4 395 false)⟩)
(.leaf ⟨167067,19,(.group 4 396 false)⟩))
(.branch 167105
(.leaf ⟨167086,19,(.group 4 397 false)⟩)
(.leaf ⟨167105,19,(.group 4 398 false)⟩)))))))

theorem tree162_checked : tree162.check 165908 167124 = true := by decide +kernel

def tree163 : Tree := (.branch 167732
(.branch 167428
(.branch 167276
(.branch 167200
(.branch 167162
(.branch 167143
(.leaf ⟨167124,19,(.group 4 399 false)⟩)
(.leaf ⟨167143,19,(.group 4 400 false)⟩))
(.branch 167181
(.leaf ⟨167162,19,(.group 4 401 false)⟩)
(.leaf ⟨167181,19,(.group 4 402 false)⟩)))
(.branch 167238
(.branch 167219
(.leaf ⟨167200,19,(.group 4 403 false)⟩)
(.leaf ⟨167219,19,(.group 4 404 false)⟩))
(.branch 167257
(.leaf ⟨167238,19,(.group 4 405 false)⟩)
(.leaf ⟨167257,19,(.group 4 406 false)⟩))))
(.branch 167352
(.branch 167314
(.branch 167295
(.leaf ⟨167276,19,(.group 4 407 false)⟩)
(.leaf ⟨167295,19,(.group 4 408 false)⟩))
(.branch 167333
(.leaf ⟨167314,19,(.group 4 409 false)⟩)
(.leaf ⟨167333,19,(.group 4 410 false)⟩)))
(.branch 167390
(.branch 167371
(.leaf ⟨167352,19,(.group 4 411 false)⟩)
(.leaf ⟨167371,19,(.group 4 412 false)⟩))
(.branch 167409
(.leaf ⟨167390,19,(.group 4 413 false)⟩)
(.leaf ⟨167409,19,(.group 4 414 false)⟩)))))
(.branch 167580
(.branch 167504
(.branch 167466
(.branch 167447
(.leaf ⟨167428,19,(.group 4 415 false)⟩)
(.leaf ⟨167447,19,(.group 4 416 false)⟩))
(.branch 167485
(.leaf ⟨167466,19,(.group 4 417 false)⟩)
(.leaf ⟨167485,19,(.group 4 418 false)⟩)))
(.branch 167542
(.branch 167523
(.leaf ⟨167504,19,(.group 4 419 false)⟩)
(.leaf ⟨167523,19,(.group 4 420 false)⟩))
(.branch 167561
(.leaf ⟨167542,19,(.group 4 421 false)⟩)
(.leaf ⟨167561,19,(.group 4 422 false)⟩))))
(.branch 167656
(.branch 167618
(.branch 167599
(.leaf ⟨167580,19,(.group 4 423 false)⟩)
(.leaf ⟨167599,19,(.group 4 424 false)⟩))
(.branch 167637
(.leaf ⟨167618,19,(.group 4 425 false)⟩)
(.leaf ⟨167637,19,(.group 4 426 false)⟩)))
(.branch 167694
(.branch 167675
(.leaf ⟨167656,19,(.group 4 427 false)⟩)
(.leaf ⟨167675,19,(.group 4 428 false)⟩))
(.branch 167713
(.leaf ⟨167694,19,(.group 4 429 false)⟩)
(.leaf ⟨167713,19,(.group 4 430 false)⟩))))))
(.branch 168036
(.branch 167884
(.branch 167808
(.branch 167770
(.branch 167751
(.leaf ⟨167732,19,(.group 4 431 false)⟩)
(.leaf ⟨167751,19,(.group 4 432 false)⟩))
(.branch 167789
(.leaf ⟨167770,19,(.group 4 433 false)⟩)
(.leaf ⟨167789,19,(.group 4 434 false)⟩)))
(.branch 167846
(.branch 167827
(.leaf ⟨167808,19,(.group 4 435 false)⟩)
(.leaf ⟨167827,19,(.group 4 436 false)⟩))
(.branch 167865
(.leaf ⟨167846,19,(.group 4 437 false)⟩)
(.leaf ⟨167865,19,(.group 4 438 false)⟩))))
(.branch 167960
(.branch 167922
(.branch 167903
(.leaf ⟨167884,19,(.group 4 439 false)⟩)
(.leaf ⟨167903,19,(.group 4 440 false)⟩))
(.branch 167941
(.leaf ⟨167922,19,(.group 4 441 false)⟩)
(.leaf ⟨167941,19,(.group 4 442 false)⟩)))
(.branch 167998
(.branch 167979
(.leaf ⟨167960,19,(.group 4 443 false)⟩)
(.leaf ⟨167979,19,(.group 4 444 false)⟩))
(.branch 168017
(.leaf ⟨167998,19,(.group 4 445 false)⟩)
(.leaf ⟨168017,19,(.group 4 446 false)⟩)))))
(.branch 168188
(.branch 168112
(.branch 168074
(.branch 168055
(.leaf ⟨168036,19,(.group 4 447 false)⟩)
(.leaf ⟨168055,19,(.group 4 448 false)⟩))
(.branch 168093
(.leaf ⟨168074,19,(.group 4 449 false)⟩)
(.leaf ⟨168093,19,(.group 4 450 false)⟩)))
(.branch 168150
(.branch 168131
(.leaf ⟨168112,19,(.group 4 451 false)⟩)
(.leaf ⟨168131,19,(.group 4 452 false)⟩))
(.branch 168169
(.leaf ⟨168150,19,(.group 4 453 false)⟩)
(.leaf ⟨168169,19,(.group 4 454 false)⟩))))
(.branch 168264
(.branch 168226
(.branch 168207
(.leaf ⟨168188,19,(.group 5 2334 false)⟩)
(.leaf ⟨168207,19,(.group 5 2335 false)⟩))
(.branch 168245
(.leaf ⟨168226,19,(.group 5 2336 false)⟩)
(.leaf ⟨168245,19,(.group 5 2337 false)⟩)))
(.branch 168302
(.branch 168283
(.leaf ⟨168264,19,(.group 5 2338 false)⟩)
(.leaf ⟨168283,19,(.group 5 2339 false)⟩))
(.branch 168321
(.leaf ⟨168302,19,(.group 5 2340 false)⟩)
(.leaf ⟨168321,19,(.group 5 2341 false)⟩)))))))

theorem tree163_checked : tree163.check 167124 168340 = true := by decide +kernel

def tree164 : Tree := (.branch 168948
(.branch 168644
(.branch 168492
(.branch 168416
(.branch 168378
(.branch 168359
(.leaf ⟨168340,19,(.group 5 2342 false)⟩)
(.leaf ⟨168359,19,(.group 5 2343 false)⟩))
(.branch 168397
(.leaf ⟨168378,19,(.group 5 2344 false)⟩)
(.leaf ⟨168397,19,(.group 5 2345 false)⟩)))
(.branch 168454
(.branch 168435
(.leaf ⟨168416,19,(.group 5 2346 false)⟩)
(.leaf ⟨168435,19,(.group 5 2347 false)⟩))
(.branch 168473
(.leaf ⟨168454,19,(.group 5 2348 false)⟩)
(.leaf ⟨168473,19,(.group 5 2349 false)⟩))))
(.branch 168568
(.branch 168530
(.branch 168511
(.leaf ⟨168492,19,(.group 5 2350 false)⟩)
(.leaf ⟨168511,19,(.group 5 2351 false)⟩))
(.branch 168549
(.leaf ⟨168530,19,(.group 5 2352 false)⟩)
(.leaf ⟨168549,19,(.group 5 2353 false)⟩)))
(.branch 168606
(.branch 168587
(.leaf ⟨168568,19,(.group 5 2354 false)⟩)
(.leaf ⟨168587,19,(.group 5 2355 false)⟩))
(.branch 168625
(.leaf ⟨168606,19,(.group 5 2356 false)⟩)
(.leaf ⟨168625,19,(.group 5 2357 false)⟩)))))
(.branch 168796
(.branch 168720
(.branch 168682
(.branch 168663
(.leaf ⟨168644,19,(.group 5 2358 false)⟩)
(.leaf ⟨168663,19,(.group 5 2359 false)⟩))
(.branch 168701
(.leaf ⟨168682,19,(.group 5 2360 false)⟩)
(.leaf ⟨168701,19,(.group 5 2361 false)⟩)))
(.branch 168758
(.branch 168739
(.leaf ⟨168720,19,(.group 5 2362 false)⟩)
(.leaf ⟨168739,19,(.group 5 2363 false)⟩))
(.branch 168777
(.leaf ⟨168758,19,(.group 5 2364 false)⟩)
(.leaf ⟨168777,19,(.group 5 2365 false)⟩))))
(.branch 168872
(.branch 168834
(.branch 168815
(.leaf ⟨168796,19,(.group 5 2366 false)⟩)
(.leaf ⟨168815,19,(.group 5 2367 false)⟩))
(.branch 168853
(.leaf ⟨168834,19,(.group 5 2368 false)⟩)
(.leaf ⟨168853,19,(.group 5 2369 false)⟩)))
(.branch 168910
(.branch 168891
(.leaf ⟨168872,19,(.group 5 2370 false)⟩)
(.leaf ⟨168891,19,(.group 5 2371 false)⟩))
(.branch 168929
(.leaf ⟨168910,19,(.group 5 2372 false)⟩)
(.leaf ⟨168929,19,(.group 5 2373 false)⟩))))))
(.branch 169252
(.branch 169100
(.branch 169024
(.branch 168986
(.branch 168967
(.leaf ⟨168948,19,(.group 5 2374 false)⟩)
(.leaf ⟨168967,19,(.group 5 2375 false)⟩))
(.branch 169005
(.leaf ⟨168986,19,(.group 5 2376 false)⟩)
(.leaf ⟨169005,19,(.group 5 2377 false)⟩)))
(.branch 169062
(.branch 169043
(.leaf ⟨169024,19,(.group 5 2378 false)⟩)
(.leaf ⟨169043,19,(.group 5 2379 false)⟩))
(.branch 169081
(.leaf ⟨169062,19,(.group 5 2380 false)⟩)
(.leaf ⟨169081,19,(.group 5 2381 false)⟩))))
(.branch 169176
(.branch 169138
(.branch 169119
(.leaf ⟨169100,19,(.group 5 2382 false)⟩)
(.leaf ⟨169119,19,(.group 5 2383 false)⟩))
(.branch 169157
(.leaf ⟨169138,19,(.group 5 2384 false)⟩)
(.leaf ⟨169157,19,(.group 5 2385 false)⟩)))
(.branch 169214
(.branch 169195
(.leaf ⟨169176,19,(.group 5 2386 false)⟩)
(.leaf ⟨169195,19,(.group 5 2387 false)⟩))
(.branch 169233
(.leaf ⟨169214,19,(.group 5 2388 false)⟩)
(.leaf ⟨169233,19,(.group 5 2389 false)⟩)))))
(.branch 169404
(.branch 169328
(.branch 169290
(.branch 169271
(.leaf ⟨169252,19,(.group 5 2390 false)⟩)
(.leaf ⟨169271,19,(.group 5 2391 false)⟩))
(.branch 169309
(.leaf ⟨169290,19,(.group 5 2392 false)⟩)
(.leaf ⟨169309,19,(.group 5 2393 false)⟩)))
(.branch 169366
(.branch 169347
(.leaf ⟨169328,19,(.group 5 2394 false)⟩)
(.leaf ⟨169347,19,(.group 5 2395 false)⟩))
(.branch 169385
(.leaf ⟨169366,19,(.group 5 2396 false)⟩)
(.leaf ⟨169385,19,(.group 5 2397 false)⟩))))
(.branch 169480
(.branch 169442
(.branch 169423
(.leaf ⟨169404,19,(.group 5 2398 false)⟩)
(.leaf ⟨169423,19,(.group 5 2399 false)⟩))
(.branch 169461
(.leaf ⟨169442,19,(.group 5 2400 false)⟩)
(.leaf ⟨169461,19,(.group 5 2401 false)⟩)))
(.branch 169518
(.branch 169499
(.leaf ⟨169480,19,(.group 5 2402 false)⟩)
(.leaf ⟨169499,19,(.group 5 2403 false)⟩))
(.branch 169537
(.leaf ⟨169518,19,(.group 5 2404 false)⟩)
(.leaf ⟨169537,19,(.group 5 2405 false)⟩)))))))

theorem tree164_checked : tree164.check 168340 169556 = true := by decide +kernel

def tree165 : Tree := (.branch 170164
(.branch 169860
(.branch 169708
(.branch 169632
(.branch 169594
(.branch 169575
(.leaf ⟨169556,19,(.group 5 2406 false)⟩)
(.leaf ⟨169575,19,(.group 5 2407 false)⟩))
(.branch 169613
(.leaf ⟨169594,19,(.group 5 2408 false)⟩)
(.leaf ⟨169613,19,(.group 5 2409 false)⟩)))
(.branch 169670
(.branch 169651
(.leaf ⟨169632,19,(.group 5 2410 false)⟩)
(.leaf ⟨169651,19,(.group 5 2411 false)⟩))
(.branch 169689
(.leaf ⟨169670,19,(.group 5 2412 false)⟩)
(.leaf ⟨169689,19,(.group 5 2413 false)⟩))))
(.branch 169784
(.branch 169746
(.branch 169727
(.leaf ⟨169708,19,(.group 5 2414 false)⟩)
(.leaf ⟨169727,19,(.group 5 2415 false)⟩))
(.branch 169765
(.leaf ⟨169746,19,(.group 5 2416 false)⟩)
(.leaf ⟨169765,19,(.group 5 2417 false)⟩)))
(.branch 169822
(.branch 169803
(.leaf ⟨169784,19,(.group 5 2418 false)⟩)
(.leaf ⟨169803,19,(.group 5 2419 false)⟩))
(.branch 169841
(.leaf ⟨169822,19,(.group 5 2420 false)⟩)
(.leaf ⟨169841,19,(.group 5 2421 false)⟩)))))
(.branch 170012
(.branch 169936
(.branch 169898
(.branch 169879
(.leaf ⟨169860,19,(.group 5 2422 false)⟩)
(.leaf ⟨169879,19,(.group 5 2423 false)⟩))
(.branch 169917
(.leaf ⟨169898,19,(.group 5 2424 false)⟩)
(.leaf ⟨169917,19,(.group 5 2425 false)⟩)))
(.branch 169974
(.branch 169955
(.leaf ⟨169936,19,(.group 5 2426 false)⟩)
(.leaf ⟨169955,19,(.group 5 2427 false)⟩))
(.branch 169993
(.leaf ⟨169974,19,(.group 5 2428 false)⟩)
(.leaf ⟨169993,19,(.group 5 2429 false)⟩))))
(.branch 170088
(.branch 170050
(.branch 170031
(.leaf ⟨170012,19,(.group 5 2430 false)⟩)
(.leaf ⟨170031,19,(.group 5 2431 false)⟩))
(.branch 170069
(.leaf ⟨170050,19,(.group 5 2432 false)⟩)
(.leaf ⟨170069,19,(.group 5 2433 false)⟩)))
(.branch 170126
(.branch 170107
(.leaf ⟨170088,19,(.group 5 2434 false)⟩)
(.leaf ⟨170107,19,(.group 5 2435 false)⟩))
(.branch 170145
(.leaf ⟨170126,19,(.group 5 2436 false)⟩)
(.leaf ⟨170145,19,(.group 5 2437 false)⟩))))))
(.branch 170468
(.branch 170316
(.branch 170240
(.branch 170202
(.branch 170183
(.leaf ⟨170164,19,(.group 5 2438 false)⟩)
(.leaf ⟨170183,19,(.group 5 2439 false)⟩))
(.branch 170221
(.leaf ⟨170202,19,(.group 5 2440 false)⟩)
(.leaf ⟨170221,19,(.group 5 2441 false)⟩)))
(.branch 170278
(.branch 170259
(.leaf ⟨170240,19,(.group 5 2442 false)⟩)
(.leaf ⟨170259,19,(.group 5 2443 false)⟩))
(.branch 170297
(.leaf ⟨170278,19,(.group 5 2444 false)⟩)
(.leaf ⟨170297,19,(.group 5 2445 false)⟩))))
(.branch 170392
(.branch 170354
(.branch 170335
(.leaf ⟨170316,19,(.group 5 2446 false)⟩)
(.leaf ⟨170335,19,(.group 5 2447 false)⟩))
(.branch 170373
(.leaf ⟨170354,19,(.group 5 2448 false)⟩)
(.leaf ⟨170373,19,(.group 5 2449 false)⟩)))
(.branch 170430
(.branch 170411
(.leaf ⟨170392,19,(.group 5 2450 false)⟩)
(.leaf ⟨170411,19,(.group 5 2451 false)⟩))
(.branch 170449
(.leaf ⟨170430,19,(.group 5 2452 false)⟩)
(.leaf ⟨170449,19,(.group 5 2453 false)⟩)))))
(.branch 170620
(.branch 170544
(.branch 170506
(.branch 170487
(.leaf ⟨170468,19,(.group 5 2454 false)⟩)
(.leaf ⟨170487,19,(.group 5 2455 false)⟩))
(.branch 170525
(.leaf ⟨170506,19,(.group 5 2456 false)⟩)
(.leaf ⟨170525,19,(.group 5 2457 false)⟩)))
(.branch 170582
(.branch 170563
(.leaf ⟨170544,19,(.group 5 2458 false)⟩)
(.leaf ⟨170563,19,(.group 5 2459 false)⟩))
(.branch 170601
(.leaf ⟨170582,19,(.group 5 2460 false)⟩)
(.leaf ⟨170601,19,(.group 5 2461 false)⟩))))
(.branch 170696
(.branch 170658
(.branch 170639
(.leaf ⟨170620,19,(.group 5 2462 false)⟩)
(.leaf ⟨170639,19,(.group 5 2463 false)⟩))
(.branch 170677
(.leaf ⟨170658,19,(.group 5 2464 false)⟩)
(.leaf ⟨170677,19,(.group 5 2465 false)⟩)))
(.branch 170734
(.branch 170715
(.leaf ⟨170696,19,(.group 5 2466 false)⟩)
(.leaf ⟨170715,19,(.group 5 2467 false)⟩))
(.branch 170753
(.leaf ⟨170734,19,(.group 5 2468 false)⟩)
(.leaf ⟨170753,19,(.group 5 2469 false)⟩)))))))

theorem tree165_checked : tree165.check 169556 170772 = true := by decide +kernel

def tree166 : Tree := (.branch 171380
(.branch 171076
(.branch 170924
(.branch 170848
(.branch 170810
(.branch 170791
(.leaf ⟨170772,19,(.group 5 2470 false)⟩)
(.leaf ⟨170791,19,(.group 5 2471 false)⟩))
(.branch 170829
(.leaf ⟨170810,19,(.group 5 2472 false)⟩)
(.leaf ⟨170829,19,(.group 5 2473 false)⟩)))
(.branch 170886
(.branch 170867
(.leaf ⟨170848,19,(.group 5 2474 false)⟩)
(.leaf ⟨170867,19,(.group 5 2475 false)⟩))
(.branch 170905
(.leaf ⟨170886,19,(.group 5 2476 false)⟩)
(.leaf ⟨170905,19,(.group 5 2477 false)⟩))))
(.branch 171000
(.branch 170962
(.branch 170943
(.leaf ⟨170924,19,(.group 5 2478 false)⟩)
(.leaf ⟨170943,19,(.group 5 2479 false)⟩))
(.branch 170981
(.leaf ⟨170962,19,(.group 5 2480 false)⟩)
(.leaf ⟨170981,19,(.group 5 2481 false)⟩)))
(.branch 171038
(.branch 171019
(.leaf ⟨171000,19,(.group 5 2482 false)⟩)
(.leaf ⟨171019,19,(.group 5 2483 false)⟩))
(.branch 171057
(.leaf ⟨171038,19,(.group 5 2484 false)⟩)
(.leaf ⟨171057,19,(.group 5 2485 false)⟩)))))
(.branch 171228
(.branch 171152
(.branch 171114
(.branch 171095
(.leaf ⟨171076,19,(.group 5 2486 false)⟩)
(.leaf ⟨171095,19,(.group 5 2487 false)⟩))
(.branch 171133
(.leaf ⟨171114,19,(.group 5 2488 false)⟩)
(.leaf ⟨171133,19,(.group 5 2489 false)⟩)))
(.branch 171190
(.branch 171171
(.leaf ⟨171152,19,(.group 5 2490 false)⟩)
(.leaf ⟨171171,19,(.group 5 2491 false)⟩))
(.branch 171209
(.leaf ⟨171190,19,(.group 5 2492 false)⟩)
(.leaf ⟨171209,19,(.group 5 2493 false)⟩))))
(.branch 171304
(.branch 171266
(.branch 171247
(.leaf ⟨171228,19,(.group 5 2494 false)⟩)
(.leaf ⟨171247,19,(.group 5 2495 false)⟩))
(.branch 171285
(.leaf ⟨171266,19,(.group 5 2496 false)⟩)
(.leaf ⟨171285,19,(.group 5 2497 false)⟩)))
(.branch 171342
(.branch 171323
(.leaf ⟨171304,19,(.group 5 2498 false)⟩)
(.leaf ⟨171323,19,(.group 5 2499 false)⟩))
(.branch 171361
(.leaf ⟨171342,19,(.group 5 2500 false)⟩)
(.leaf ⟨171361,19,(.group 5 2501 false)⟩))))))
(.branch 171684
(.branch 171532
(.branch 171456
(.branch 171418
(.branch 171399
(.leaf ⟨171380,19,(.group 5 2502 false)⟩)
(.leaf ⟨171399,19,(.group 5 2503 false)⟩))
(.branch 171437
(.leaf ⟨171418,19,(.group 5 2504 false)⟩)
(.leaf ⟨171437,19,(.group 5 2505 false)⟩)))
(.branch 171494
(.branch 171475
(.leaf ⟨171456,19,(.group 5 2506 false)⟩)
(.leaf ⟨171475,19,(.group 5 2507 false)⟩))
(.branch 171513
(.leaf ⟨171494,19,(.group 5 2508 false)⟩)
(.leaf ⟨171513,19,(.group 5 2509 false)⟩))))
(.branch 171608
(.branch 171570
(.branch 171551
(.leaf ⟨171532,19,(.group 5 2510 false)⟩)
(.leaf ⟨171551,19,(.group 5 2511 false)⟩))
(.branch 171589
(.leaf ⟨171570,19,(.group 5 2512 false)⟩)
(.leaf ⟨171589,19,(.group 5 2513 false)⟩)))
(.branch 171646
(.branch 171627
(.leaf ⟨171608,19,(.group 5 2514 false)⟩)
(.leaf ⟨171627,19,(.group 5 2515 false)⟩))
(.branch 171665
(.leaf ⟨171646,19,(.group 5 2516 false)⟩)
(.leaf ⟨171665,19,(.group 5 2517 false)⟩)))))
(.branch 171836
(.branch 171760
(.branch 171722
(.branch 171703
(.leaf ⟨171684,19,(.group 5 2518 false)⟩)
(.leaf ⟨171703,19,(.group 5 2519 false)⟩))
(.branch 171741
(.leaf ⟨171722,19,(.group 5 2520 false)⟩)
(.leaf ⟨171741,19,(.group 5 2521 false)⟩)))
(.branch 171798
(.branch 171779
(.leaf ⟨171760,19,(.group 5 2522 false)⟩)
(.leaf ⟨171779,19,(.group 5 2523 false)⟩))
(.branch 171817
(.leaf ⟨171798,19,(.group 5 2524 false)⟩)
(.leaf ⟨171817,19,(.group 5 2525 false)⟩))))
(.branch 171912
(.branch 171874
(.branch 171855
(.leaf ⟨171836,19,(.group 5 2526 false)⟩)
(.leaf ⟨171855,19,(.group 5 2527 false)⟩))
(.branch 171893
(.leaf ⟨171874,19,(.group 5 2528 false)⟩)
(.leaf ⟨171893,19,(.group 5 2529 false)⟩)))
(.branch 171950
(.branch 171931
(.leaf ⟨171912,19,(.group 5 2530 false)⟩)
(.leaf ⟨171931,19,(.group 5 2531 false)⟩))
(.branch 171969
(.leaf ⟨171950,19,(.group 5 2532 false)⟩)
(.leaf ⟨171969,19,(.group 5 2533 false)⟩)))))))

theorem tree166_checked : tree166.check 170772 171988 = true := by decide +kernel

def tree167 : Tree := (.branch 172596
(.branch 172292
(.branch 172140
(.branch 172064
(.branch 172026
(.branch 172007
(.leaf ⟨171988,19,(.group 5 2534 false)⟩)
(.leaf ⟨172007,19,(.group 5 2535 false)⟩))
(.branch 172045
(.leaf ⟨172026,19,(.group 5 2536 false)⟩)
(.leaf ⟨172045,19,(.group 5 2537 false)⟩)))
(.branch 172102
(.branch 172083
(.leaf ⟨172064,19,(.group 5 2538 false)⟩)
(.leaf ⟨172083,19,(.group 5 2539 false)⟩))
(.branch 172121
(.leaf ⟨172102,19,(.group 5 2540 false)⟩)
(.leaf ⟨172121,19,(.group 5 2541 false)⟩))))
(.branch 172216
(.branch 172178
(.branch 172159
(.leaf ⟨172140,19,(.group 5 2542 false)⟩)
(.leaf ⟨172159,19,(.group 5 2543 false)⟩))
(.branch 172197
(.leaf ⟨172178,19,(.group 5 2544 false)⟩)
(.leaf ⟨172197,19,(.group 5 2545 false)⟩)))
(.branch 172254
(.branch 172235
(.leaf ⟨172216,19,(.group 5 2546 false)⟩)
(.leaf ⟨172235,19,(.group 5 2547 false)⟩))
(.branch 172273
(.leaf ⟨172254,19,(.group 5 2548 false)⟩)
(.leaf ⟨172273,19,(.group 5 2549 false)⟩)))))
(.branch 172444
(.branch 172368
(.branch 172330
(.branch 172311
(.leaf ⟨172292,19,(.group 5 2550 false)⟩)
(.leaf ⟨172311,19,(.group 5 2551 false)⟩))
(.branch 172349
(.leaf ⟨172330,19,(.group 5 2552 false)⟩)
(.leaf ⟨172349,19,(.group 5 2553 false)⟩)))
(.branch 172406
(.branch 172387
(.leaf ⟨172368,19,(.group 5 2554 false)⟩)
(.leaf ⟨172387,19,(.group 5 2555 false)⟩))
(.branch 172425
(.leaf ⟨172406,19,(.group 5 2556 false)⟩)
(.leaf ⟨172425,19,(.group 5 2557 false)⟩))))
(.branch 172520
(.branch 172482
(.branch 172463
(.leaf ⟨172444,19,(.group 5 2558 false)⟩)
(.leaf ⟨172463,19,(.group 5 2559 false)⟩))
(.branch 172501
(.leaf ⟨172482,19,(.group 5 2560 false)⟩)
(.leaf ⟨172501,19,(.group 5 2561 false)⟩)))
(.branch 172558
(.branch 172539
(.leaf ⟨172520,19,(.group 5 2562 false)⟩)
(.leaf ⟨172539,19,(.group 5 2563 false)⟩))
(.branch 172577
(.leaf ⟨172558,19,(.group 5 2564 false)⟩)
(.leaf ⟨172577,19,(.group 5 2565 false)⟩))))))
(.branch 172900
(.branch 172748
(.branch 172672
(.branch 172634
(.branch 172615
(.leaf ⟨172596,19,(.group 5 2566 false)⟩)
(.leaf ⟨172615,19,(.group 5 2567 false)⟩))
(.branch 172653
(.leaf ⟨172634,19,(.group 5 2568 false)⟩)
(.leaf ⟨172653,19,(.group 5 2569 false)⟩)))
(.branch 172710
(.branch 172691
(.leaf ⟨172672,19,(.group 5 2570 false)⟩)
(.leaf ⟨172691,19,(.group 5 2571 false)⟩))
(.branch 172729
(.leaf ⟨172710,19,(.group 5 2572 false)⟩)
(.leaf ⟨172729,19,(.group 5 2573 false)⟩))))
(.branch 172824
(.branch 172786
(.branch 172767
(.leaf ⟨172748,19,(.group 5 2574 false)⟩)
(.leaf ⟨172767,19,(.group 5 2575 false)⟩))
(.branch 172805
(.leaf ⟨172786,19,(.group 5 2576 false)⟩)
(.leaf ⟨172805,19,(.group 5 2577 false)⟩)))
(.branch 172862
(.branch 172843
(.leaf ⟨172824,19,(.group 5 2578 false)⟩)
(.leaf ⟨172843,19,(.group 5 2579 false)⟩))
(.branch 172881
(.leaf ⟨172862,19,(.group 5 2580 false)⟩)
(.leaf ⟨172881,19,(.group 5 2581 false)⟩)))))
(.branch 173052
(.branch 172976
(.branch 172938
(.branch 172919
(.leaf ⟨172900,19,(.group 5 2582 false)⟩)
(.leaf ⟨172919,19,(.group 5 2583 false)⟩))
(.branch 172957
(.leaf ⟨172938,19,(.group 5 2584 false)⟩)
(.leaf ⟨172957,19,(.group 5 2585 false)⟩)))
(.branch 173014
(.branch 172995
(.leaf ⟨172976,19,(.group 5 2586 false)⟩)
(.leaf ⟨172995,19,(.group 5 2587 false)⟩))
(.branch 173033
(.leaf ⟨173014,19,(.group 5 2588 false)⟩)
(.leaf ⟨173033,19,(.group 5 2589 false)⟩))))
(.branch 173128
(.branch 173090
(.branch 173071
(.leaf ⟨173052,19,(.group 5 2590 false)⟩)
(.leaf ⟨173071,19,(.group 5 2591 false)⟩))
(.branch 173109
(.leaf ⟨173090,19,(.group 5 2592 false)⟩)
(.leaf ⟨173109,19,(.group 5 2593 false)⟩)))
(.branch 173166
(.branch 173147
(.leaf ⟨173128,19,(.group 5 2594 false)⟩)
(.leaf ⟨173147,19,(.group 5 2595 false)⟩))
(.branch 173185
(.leaf ⟨173166,19,(.group 5 2596 false)⟩)
(.leaf ⟨173185,19,(.group 5 2597 false)⟩)))))))

theorem tree167_checked : tree167.check 171988 173204 = true := by decide +kernel

def tree168 : Tree := (.branch 173812
(.branch 173508
(.branch 173356
(.branch 173280
(.branch 173242
(.branch 173223
(.leaf ⟨173204,19,(.group 5 2598 false)⟩)
(.leaf ⟨173223,19,(.group 5 2599 false)⟩))
(.branch 173261
(.leaf ⟨173242,19,(.group 5 2600 false)⟩)
(.leaf ⟨173261,19,(.group 5 2601 false)⟩)))
(.branch 173318
(.branch 173299
(.leaf ⟨173280,19,(.group 5 2602 false)⟩)
(.leaf ⟨173299,19,(.group 5 2603 false)⟩))
(.branch 173337
(.leaf ⟨173318,19,(.group 5 2604 false)⟩)
(.leaf ⟨173337,19,(.group 5 2605 false)⟩))))
(.branch 173432
(.branch 173394
(.branch 173375
(.leaf ⟨173356,19,(.group 5 2606 false)⟩)
(.leaf ⟨173375,19,(.group 5 2607 false)⟩))
(.branch 173413
(.leaf ⟨173394,19,(.group 5 2608 false)⟩)
(.leaf ⟨173413,19,(.group 5 2609 false)⟩)))
(.branch 173470
(.branch 173451
(.leaf ⟨173432,19,(.group 5 2610 false)⟩)
(.leaf ⟨173451,19,(.group 5 2611 false)⟩))
(.branch 173489
(.leaf ⟨173470,19,(.group 5 2612 false)⟩)
(.leaf ⟨173489,19,(.group 5 2613 false)⟩)))))
(.branch 173660
(.branch 173584
(.branch 173546
(.branch 173527
(.leaf ⟨173508,19,(.group 5 2614 false)⟩)
(.leaf ⟨173527,19,(.group 5 2615 false)⟩))
(.branch 173565
(.leaf ⟨173546,19,(.group 5 2616 false)⟩)
(.leaf ⟨173565,19,(.group 5 2617 false)⟩)))
(.branch 173622
(.branch 173603
(.leaf ⟨173584,19,(.group 5 2618 false)⟩)
(.leaf ⟨173603,19,(.group 5 2619 false)⟩))
(.branch 173641
(.leaf ⟨173622,19,(.group 5 2620 false)⟩)
(.leaf ⟨173641,19,(.group 5 2621 false)⟩))))
(.branch 173736
(.branch 173698
(.branch 173679
(.leaf ⟨173660,19,(.group 5 2622 false)⟩)
(.leaf ⟨173679,19,(.group 5 2623 false)⟩))
(.branch 173717
(.leaf ⟨173698,19,(.group 5 2624 false)⟩)
(.leaf ⟨173717,19,(.group 5 2625 false)⟩)))
(.branch 173774
(.branch 173755
(.leaf ⟨173736,19,(.group 5 2626 false)⟩)
(.leaf ⟨173755,19,(.group 5 2627 false)⟩))
(.branch 173793
(.leaf ⟨173774,19,(.group 5 2628 false)⟩)
(.leaf ⟨173793,19,(.group 5 2629 false)⟩))))))
(.branch 174116
(.branch 173964
(.branch 173888
(.branch 173850
(.branch 173831
(.leaf ⟨173812,19,(.group 5 2630 false)⟩)
(.leaf ⟨173831,19,(.group 5 2631 false)⟩))
(.branch 173869
(.leaf ⟨173850,19,(.group 5 2632 false)⟩)
(.leaf ⟨173869,19,(.group 5 2633 false)⟩)))
(.branch 173926
(.branch 173907
(.leaf ⟨173888,19,(.group 5 2634 false)⟩)
(.leaf ⟨173907,19,(.group 5 2635 false)⟩))
(.branch 173945
(.leaf ⟨173926,19,(.group 5 2636 false)⟩)
(.leaf ⟨173945,19,(.group 5 2637 false)⟩))))
(.branch 174040
(.branch 174002
(.branch 173983
(.leaf ⟨173964,19,(.group 5 2638 false)⟩)
(.leaf ⟨173983,19,(.group 5 2639 false)⟩))
(.branch 174021
(.leaf ⟨174002,19,(.group 5 2640 false)⟩)
(.leaf ⟨174021,19,(.group 5 2641 false)⟩)))
(.branch 174078
(.branch 174059
(.leaf ⟨174040,19,(.group 5 2642 false)⟩)
(.leaf ⟨174059,19,(.group 5 2643 false)⟩))
(.branch 174097
(.leaf ⟨174078,19,(.group 5 2644 false)⟩)
(.leaf ⟨174097,19,(.group 5 2645 false)⟩)))))
(.branch 174268
(.branch 174192
(.branch 174154
(.branch 174135
(.leaf ⟨174116,19,(.group 5 2646 false)⟩)
(.leaf ⟨174135,19,(.group 5 2647 false)⟩))
(.branch 174173
(.leaf ⟨174154,19,(.group 5 2648 false)⟩)
(.leaf ⟨174173,19,(.group 5 2649 false)⟩)))
(.branch 174230
(.branch 174211
(.leaf ⟨174192,19,(.group 5 2650 false)⟩)
(.leaf ⟨174211,19,(.group 5 2651 false)⟩))
(.branch 174249
(.leaf ⟨174230,19,(.group 5 2652 false)⟩)
(.leaf ⟨174249,19,(.group 5 2653 false)⟩))))
(.branch 174344
(.branch 174306
(.branch 174287
(.leaf ⟨174268,19,(.group 5 2654 false)⟩)
(.leaf ⟨174287,19,(.group 5 2655 false)⟩))
(.branch 174325
(.leaf ⟨174306,19,(.group 5 2656 false)⟩)
(.leaf ⟨174325,19,(.group 5 2657 false)⟩)))
(.branch 174382
(.branch 174363
(.leaf ⟨174344,19,(.group 5 2658 false)⟩)
(.leaf ⟨174363,19,(.group 5 2659 false)⟩))
(.branch 174401
(.leaf ⟨174382,19,(.group 5 2660 false)⟩)
(.leaf ⟨174401,19,(.group 5 2661 false)⟩)))))))

theorem tree168_checked : tree168.check 173204 174420 = true := by decide +kernel

def tree169 : Tree := (.branch 175028
(.branch 174724
(.branch 174572
(.branch 174496
(.branch 174458
(.branch 174439
(.leaf ⟨174420,19,(.group 5 2662 false)⟩)
(.leaf ⟨174439,19,(.group 5 2663 false)⟩))
(.branch 174477
(.leaf ⟨174458,19,(.group 5 2664 false)⟩)
(.leaf ⟨174477,19,(.group 5 2665 false)⟩)))
(.branch 174534
(.branch 174515
(.leaf ⟨174496,19,(.group 5 2666 false)⟩)
(.leaf ⟨174515,19,(.group 5 2667 false)⟩))
(.branch 174553
(.leaf ⟨174534,19,(.group 5 2668 false)⟩)
(.leaf ⟨174553,19,(.group 5 2669 false)⟩))))
(.branch 174648
(.branch 174610
(.branch 174591
(.leaf ⟨174572,19,(.group 5 2670 false)⟩)
(.leaf ⟨174591,19,(.group 5 2671 false)⟩))
(.branch 174629
(.leaf ⟨174610,19,(.group 5 2672 false)⟩)
(.leaf ⟨174629,19,(.group 5 2673 false)⟩)))
(.branch 174686
(.branch 174667
(.leaf ⟨174648,19,(.group 5 2674 false)⟩)
(.leaf ⟨174667,19,(.group 5 2675 false)⟩))
(.branch 174705
(.leaf ⟨174686,19,(.group 5 2676 false)⟩)
(.leaf ⟨174705,19,(.group 5 2677 false)⟩)))))
(.branch 174876
(.branch 174800
(.branch 174762
(.branch 174743
(.leaf ⟨174724,19,(.group 5 2678 false)⟩)
(.leaf ⟨174743,19,(.group 5 2679 false)⟩))
(.branch 174781
(.leaf ⟨174762,19,(.group 5 2680 false)⟩)
(.leaf ⟨174781,19,(.group 5 2681 false)⟩)))
(.branch 174838
(.branch 174819
(.leaf ⟨174800,19,(.group 5 2682 false)⟩)
(.leaf ⟨174819,19,(.group 5 2683 false)⟩))
(.branch 174857
(.leaf ⟨174838,19,(.group 5 2684 false)⟩)
(.leaf ⟨174857,19,(.group 5 2685 false)⟩))))
(.branch 174952
(.branch 174914
(.branch 174895
(.leaf ⟨174876,19,(.group 5 2686 false)⟩)
(.leaf ⟨174895,19,(.group 5 2687 false)⟩))
(.branch 174933
(.leaf ⟨174914,19,(.group 5 2688 false)⟩)
(.leaf ⟨174933,19,(.group 5 2689 false)⟩)))
(.branch 174990
(.branch 174971
(.leaf ⟨174952,19,(.group 5 2690 false)⟩)
(.leaf ⟨174971,19,(.group 5 2691 false)⟩))
(.branch 175009
(.leaf ⟨174990,19,(.group 5 2692 false)⟩)
(.leaf ⟨175009,19,(.group 5 2693 false)⟩))))))
(.branch 175332
(.branch 175180
(.branch 175104
(.branch 175066
(.branch 175047
(.leaf ⟨175028,19,(.group 5 2694 false)⟩)
(.leaf ⟨175047,19,(.group 5 2695 false)⟩))
(.branch 175085
(.leaf ⟨175066,19,(.group 5 2696 false)⟩)
(.leaf ⟨175085,19,(.group 5 2697 false)⟩)))
(.branch 175142
(.branch 175123
(.leaf ⟨175104,19,(.group 5 2698 false)⟩)
(.leaf ⟨175123,19,(.group 5 2699 false)⟩))
(.branch 175161
(.leaf ⟨175142,19,(.group 5 2700 false)⟩)
(.leaf ⟨175161,19,(.group 5 2701 false)⟩))))
(.branch 175256
(.branch 175218
(.branch 175199
(.leaf ⟨175180,19,(.group 5 2702 false)⟩)
(.leaf ⟨175199,19,(.group 5 2703 false)⟩))
(.branch 175237
(.leaf ⟨175218,19,(.group 5 2704 false)⟩)
(.leaf ⟨175237,19,(.group 5 2705 false)⟩)))
(.branch 175294
(.branch 175275
(.leaf ⟨175256,19,(.group 5 2706 false)⟩)
(.leaf ⟨175275,19,(.group 5 2707 false)⟩))
(.branch 175313
(.leaf ⟨175294,19,(.group 5 2708 false)⟩)
(.leaf ⟨175313,19,(.group 5 2709 false)⟩)))))
(.branch 175484
(.branch 175408
(.branch 175370
(.branch 175351
(.leaf ⟨175332,19,(.group 5 2710 false)⟩)
(.leaf ⟨175351,19,(.group 5 2711 false)⟩))
(.branch 175389
(.leaf ⟨175370,19,(.group 5 2712 false)⟩)
(.leaf ⟨175389,19,(.group 5 2713 false)⟩)))
(.branch 175446
(.branch 175427
(.leaf ⟨175408,19,(.group 5 2714 false)⟩)
(.leaf ⟨175427,19,(.group 5 2715 false)⟩))
(.branch 175465
(.leaf ⟨175446,19,(.group 5 2716 false)⟩)
(.leaf ⟨175465,19,(.group 5 2717 false)⟩))))
(.branch 175560
(.branch 175522
(.branch 175503
(.leaf ⟨175484,19,(.group 5 2718 false)⟩)
(.leaf ⟨175503,19,(.group 5 2719 false)⟩))
(.branch 175541
(.leaf ⟨175522,19,(.group 5 2720 false)⟩)
(.leaf ⟨175541,19,(.group 5 2721 false)⟩)))
(.branch 175598
(.branch 175579
(.leaf ⟨175560,19,(.group 5 2722 false)⟩)
(.leaf ⟨175579,19,(.group 5 2723 false)⟩))
(.branch 175617
(.leaf ⟨175598,19,(.group 5 2724 false)⟩)
(.leaf ⟨175617,19,(.group 5 2725 false)⟩)))))))

theorem tree169_checked : tree169.check 174420 175636 = true := by decide +kernel

def tree170 : Tree := (.branch 176244
(.branch 175940
(.branch 175788
(.branch 175712
(.branch 175674
(.branch 175655
(.leaf ⟨175636,19,(.group 5 2726 false)⟩)
(.leaf ⟨175655,19,(.group 5 2727 false)⟩))
(.branch 175693
(.leaf ⟨175674,19,(.group 5 2728 false)⟩)
(.leaf ⟨175693,19,(.group 5 2729 false)⟩)))
(.branch 175750
(.branch 175731
(.leaf ⟨175712,19,(.group 5 2730 false)⟩)
(.leaf ⟨175731,19,(.group 5 2731 false)⟩))
(.branch 175769
(.leaf ⟨175750,19,(.group 5 2732 false)⟩)
(.leaf ⟨175769,19,(.group 5 2733 false)⟩))))
(.branch 175864
(.branch 175826
(.branch 175807
(.leaf ⟨175788,19,(.group 5 2734 false)⟩)
(.leaf ⟨175807,19,(.group 5 2735 false)⟩))
(.branch 175845
(.leaf ⟨175826,19,(.group 5 2736 false)⟩)
(.leaf ⟨175845,19,(.group 5 2737 false)⟩)))
(.branch 175902
(.branch 175883
(.leaf ⟨175864,19,(.group 5 2738 false)⟩)
(.leaf ⟨175883,19,(.group 5 2739 false)⟩))
(.branch 175921
(.leaf ⟨175902,19,(.group 5 2740 false)⟩)
(.leaf ⟨175921,19,(.group 5 2741 false)⟩)))))
(.branch 176092
(.branch 176016
(.branch 175978
(.branch 175959
(.leaf ⟨175940,19,(.group 5 2742 false)⟩)
(.leaf ⟨175959,19,(.group 5 2743 false)⟩))
(.branch 175997
(.leaf ⟨175978,19,(.group 5 2744 false)⟩)
(.leaf ⟨175997,19,(.group 5 2745 false)⟩)))
(.branch 176054
(.branch 176035
(.leaf ⟨176016,19,(.group 5 2746 false)⟩)
(.leaf ⟨176035,19,(.group 5 2747 false)⟩))
(.branch 176073
(.leaf ⟨176054,19,(.group 5 2748 false)⟩)
(.leaf ⟨176073,19,(.group 5 2749 false)⟩))))
(.branch 176168
(.branch 176130
(.branch 176111
(.leaf ⟨176092,19,(.group 5 2750 false)⟩)
(.leaf ⟨176111,19,(.group 5 2751 false)⟩))
(.branch 176149
(.leaf ⟨176130,19,(.group 5 2752 false)⟩)
(.leaf ⟨176149,19,(.group 5 2753 false)⟩)))
(.branch 176206
(.branch 176187
(.leaf ⟨176168,19,(.group 5 2754 false)⟩)
(.leaf ⟨176187,19,(.group 5 2755 false)⟩))
(.branch 176225
(.leaf ⟨176206,19,(.group 5 2756 false)⟩)
(.leaf ⟨176225,19,(.group 5 2757 false)⟩))))))
(.branch 176548
(.branch 176396
(.branch 176320
(.branch 176282
(.branch 176263
(.leaf ⟨176244,19,(.group 5 2758 false)⟩)
(.leaf ⟨176263,19,(.group 5 2759 false)⟩))
(.branch 176301
(.leaf ⟨176282,19,(.group 5 2760 false)⟩)
(.leaf ⟨176301,19,(.group 5 2761 false)⟩)))
(.branch 176358
(.branch 176339
(.leaf ⟨176320,19,(.group 5 2762 false)⟩)
(.leaf ⟨176339,19,(.group 5 2763 false)⟩))
(.branch 176377
(.leaf ⟨176358,19,(.group 5 2764 false)⟩)
(.leaf ⟨176377,19,(.group 5 2765 false)⟩))))
(.branch 176472
(.branch 176434
(.branch 176415
(.leaf ⟨176396,19,(.group 5 2766 false)⟩)
(.leaf ⟨176415,19,(.group 5 2767 false)⟩))
(.branch 176453
(.leaf ⟨176434,19,(.group 5 2768 false)⟩)
(.leaf ⟨176453,19,(.group 5 2769 false)⟩)))
(.branch 176510
(.branch 176491
(.leaf ⟨176472,19,(.group 5 2770 false)⟩)
(.leaf ⟨176491,19,(.group 5 2771 false)⟩))
(.branch 176529
(.leaf ⟨176510,19,(.group 5 2772 false)⟩)
(.leaf ⟨176529,19,(.group 5 2773 false)⟩)))))
(.branch 176700
(.branch 176624
(.branch 176586
(.branch 176567
(.leaf ⟨176548,19,(.group 5 2774 false)⟩)
(.leaf ⟨176567,19,(.group 5 2775 false)⟩))
(.branch 176605
(.leaf ⟨176586,19,(.group 5 2776 false)⟩)
(.leaf ⟨176605,19,(.group 5 2777 false)⟩)))
(.branch 176662
(.branch 176643
(.leaf ⟨176624,19,(.group 5 2778 false)⟩)
(.leaf ⟨176643,19,(.group 5 2779 false)⟩))
(.branch 176681
(.leaf ⟨176662,19,(.group 5 2780 false)⟩)
(.leaf ⟨176681,19,(.group 5 2781 false)⟩))))
(.branch 176776
(.branch 176738
(.branch 176719
(.leaf ⟨176700,19,(.group 5 2782 false)⟩)
(.leaf ⟨176719,19,(.group 5 2783 false)⟩))
(.branch 176757
(.leaf ⟨176738,19,(.group 5 2784 false)⟩)
(.leaf ⟨176757,19,(.group 5 2785 false)⟩)))
(.branch 176814
(.branch 176795
(.leaf ⟨176776,19,(.group 5 2786 false)⟩)
(.leaf ⟨176795,19,(.group 5 2787 false)⟩))
(.branch 176833
(.leaf ⟨176814,19,(.group 5 2788 false)⟩)
(.leaf ⟨176833,19,(.group 5 2789 false)⟩)))))))

theorem tree170_checked : tree170.check 175636 176852 = true := by decide +kernel

def tree171 : Tree := (.branch 177460
(.branch 177156
(.branch 177004
(.branch 176928
(.branch 176890
(.branch 176871
(.leaf ⟨176852,19,(.group 5 2790 false)⟩)
(.leaf ⟨176871,19,(.group 5 2791 false)⟩))
(.branch 176909
(.leaf ⟨176890,19,(.group 5 2792 false)⟩)
(.leaf ⟨176909,19,(.group 5 2793 false)⟩)))
(.branch 176966
(.branch 176947
(.leaf ⟨176928,19,(.group 5 2794 false)⟩)
(.leaf ⟨176947,19,(.group 5 2795 false)⟩))
(.branch 176985
(.leaf ⟨176966,19,(.group 5 2796 false)⟩)
(.leaf ⟨176985,19,(.group 5 2797 false)⟩))))
(.branch 177080
(.branch 177042
(.branch 177023
(.leaf ⟨177004,19,(.group 5 2798 false)⟩)
(.leaf ⟨177023,19,(.group 5 2799 false)⟩))
(.branch 177061
(.leaf ⟨177042,19,(.group 5 2800 false)⟩)
(.leaf ⟨177061,19,(.group 5 2801 false)⟩)))
(.branch 177118
(.branch 177099
(.leaf ⟨177080,19,(.group 5 2802 false)⟩)
(.leaf ⟨177099,19,(.group 5 2803 false)⟩))
(.branch 177137
(.leaf ⟨177118,19,(.group 5 2804 false)⟩)
(.leaf ⟨177137,19,(.group 5 2805 false)⟩)))))
(.branch 177308
(.branch 177232
(.branch 177194
(.branch 177175
(.leaf ⟨177156,19,(.group 5 2806 false)⟩)
(.leaf ⟨177175,19,(.group 5 2807 false)⟩))
(.branch 177213
(.leaf ⟨177194,19,(.group 5 2808 false)⟩)
(.leaf ⟨177213,19,(.group 5 2809 false)⟩)))
(.branch 177270
(.branch 177251
(.leaf ⟨177232,19,(.group 5 2810 false)⟩)
(.leaf ⟨177251,19,(.group 5 2811 false)⟩))
(.branch 177289
(.leaf ⟨177270,19,(.group 5 2812 false)⟩)
(.leaf ⟨177289,19,(.group 5 2813 false)⟩))))
(.branch 177384
(.branch 177346
(.branch 177327
(.leaf ⟨177308,19,(.group 5 2814 false)⟩)
(.leaf ⟨177327,19,(.group 5 2815 false)⟩))
(.branch 177365
(.leaf ⟨177346,19,(.group 5 2816 false)⟩)
(.leaf ⟨177365,19,(.group 5 2817 false)⟩)))
(.branch 177422
(.branch 177403
(.leaf ⟨177384,19,(.group 5 2818 false)⟩)
(.leaf ⟨177403,19,(.group 5 2819 false)⟩))
(.branch 177441
(.leaf ⟨177422,19,(.group 5 2820 false)⟩)
(.leaf ⟨177441,19,(.group 5 2821 false)⟩))))))
(.branch 177764
(.branch 177612
(.branch 177536
(.branch 177498
(.branch 177479
(.leaf ⟨177460,19,(.group 5 2822 false)⟩)
(.leaf ⟨177479,19,(.group 5 2823 false)⟩))
(.branch 177517
(.leaf ⟨177498,19,(.group 5 2824 false)⟩)
(.leaf ⟨177517,19,(.group 5 2825 false)⟩)))
(.branch 177574
(.branch 177555
(.leaf ⟨177536,19,(.group 5 2826 false)⟩)
(.leaf ⟨177555,19,(.group 5 2827 false)⟩))
(.branch 177593
(.leaf ⟨177574,19,(.group 5 2828 false)⟩)
(.leaf ⟨177593,19,(.group 5 2829 false)⟩))))
(.branch 177688
(.branch 177650
(.branch 177631
(.leaf ⟨177612,19,(.group 5 2830 false)⟩)
(.leaf ⟨177631,19,(.group 5 2831 false)⟩))
(.branch 177669
(.leaf ⟨177650,19,(.group 5 2832 false)⟩)
(.leaf ⟨177669,19,(.group 5 2833 false)⟩)))
(.branch 177726
(.branch 177707
(.leaf ⟨177688,19,(.group 5 2834 false)⟩)
(.leaf ⟨177707,19,(.group 5 2835 false)⟩))
(.branch 177745
(.leaf ⟨177726,19,(.group 5 2836 false)⟩)
(.leaf ⟨177745,19,(.group 5 2837 false)⟩)))))
(.branch 177916
(.branch 177840
(.branch 177802
(.branch 177783
(.leaf ⟨177764,19,(.group 5 2838 false)⟩)
(.leaf ⟨177783,19,(.group 5 2839 false)⟩))
(.branch 177821
(.leaf ⟨177802,19,(.group 5 2840 false)⟩)
(.leaf ⟨177821,19,(.group 5 2841 false)⟩)))
(.branch 177878
(.branch 177859
(.leaf ⟨177840,19,(.group 5 2842 false)⟩)
(.leaf ⟨177859,19,(.group 5 2843 false)⟩))
(.branch 177897
(.leaf ⟨177878,19,(.group 5 2844 false)⟩)
(.leaf ⟨177897,19,(.group 5 2845 false)⟩))))
(.branch 177992
(.branch 177954
(.branch 177935
(.leaf ⟨177916,19,(.group 5 2846 false)⟩)
(.leaf ⟨177935,19,(.group 5 2847 false)⟩))
(.branch 177973
(.leaf ⟨177954,19,(.group 5 2848 false)⟩)
(.leaf ⟨177973,19,(.group 5 2849 false)⟩)))
(.branch 178030
(.branch 178011
(.leaf ⟨177992,19,(.group 5 2850 false)⟩)
(.leaf ⟨178011,19,(.group 5 2851 false)⟩))
(.branch 178049
(.leaf ⟨178030,19,(.group 5 2852 false)⟩)
(.leaf ⟨178049,19,(.group 5 2853 false)⟩)))))))

theorem tree171_checked : tree171.check 176852 178068 = true := by decide +kernel

def tree172 : Tree := (.branch 178676
(.branch 178372
(.branch 178220
(.branch 178144
(.branch 178106
(.branch 178087
(.leaf ⟨178068,19,(.group 5 2854 false)⟩)
(.leaf ⟨178087,19,(.group 5 2855 false)⟩))
(.branch 178125
(.leaf ⟨178106,19,(.group 5 2856 false)⟩)
(.leaf ⟨178125,19,(.group 5 2857 false)⟩)))
(.branch 178182
(.branch 178163
(.leaf ⟨178144,19,(.group 5 2858 false)⟩)
(.leaf ⟨178163,19,(.group 5 2859 false)⟩))
(.branch 178201
(.leaf ⟨178182,19,(.group 5 2860 false)⟩)
(.leaf ⟨178201,19,(.group 5 2861 false)⟩))))
(.branch 178296
(.branch 178258
(.branch 178239
(.leaf ⟨178220,19,(.group 5 2862 false)⟩)
(.leaf ⟨178239,19,(.group 5 2863 false)⟩))
(.branch 178277
(.leaf ⟨178258,19,(.group 5 2864 false)⟩)
(.leaf ⟨178277,19,(.group 5 2865 false)⟩)))
(.branch 178334
(.branch 178315
(.leaf ⟨178296,19,(.group 5 2866 false)⟩)
(.leaf ⟨178315,19,(.group 5 2867 false)⟩))
(.branch 178353
(.leaf ⟨178334,19,(.group 5 2868 false)⟩)
(.leaf ⟨178353,19,(.group 5 2869 false)⟩)))))
(.branch 178524
(.branch 178448
(.branch 178410
(.branch 178391
(.leaf ⟨178372,19,(.group 5 2870 false)⟩)
(.leaf ⟨178391,19,(.group 5 2871 false)⟩))
(.branch 178429
(.leaf ⟨178410,19,(.group 5 2872 false)⟩)
(.leaf ⟨178429,19,(.group 5 2873 false)⟩)))
(.branch 178486
(.branch 178467
(.leaf ⟨178448,19,(.group 5 2874 false)⟩)
(.leaf ⟨178467,19,(.group 5 2875 false)⟩))
(.branch 178505
(.leaf ⟨178486,19,(.group 5 2876 false)⟩)
(.leaf ⟨178505,19,(.group 5 2877 false)⟩))))
(.branch 178600
(.branch 178562
(.branch 178543
(.leaf ⟨178524,19,(.group 5 2878 false)⟩)
(.leaf ⟨178543,19,(.group 5 2879 false)⟩))
(.branch 178581
(.leaf ⟨178562,19,(.group 5 2880 false)⟩)
(.leaf ⟨178581,19,(.group 5 2881 false)⟩)))
(.branch 178638
(.branch 178619
(.leaf ⟨178600,19,(.group 5 2882 false)⟩)
(.leaf ⟨178619,19,(.group 5 2883 false)⟩))
(.branch 178657
(.leaf ⟨178638,19,(.group 5 2884 false)⟩)
(.leaf ⟨178657,19,(.group 5 2885 false)⟩))))))
(.branch 178980
(.branch 178828
(.branch 178752
(.branch 178714
(.branch 178695
(.leaf ⟨178676,19,(.group 5 2886 false)⟩)
(.leaf ⟨178695,19,(.group 5 2887 false)⟩))
(.branch 178733
(.leaf ⟨178714,19,(.group 5 2888 false)⟩)
(.leaf ⟨178733,19,(.group 5 2889 false)⟩)))
(.branch 178790
(.branch 178771
(.leaf ⟨178752,19,(.group 5 2890 false)⟩)
(.leaf ⟨178771,19,(.group 5 2891 false)⟩))
(.branch 178809
(.leaf ⟨178790,19,(.group 5 2892 false)⟩)
(.leaf ⟨178809,19,(.group 5 2893 false)⟩))))
(.branch 178904
(.branch 178866
(.branch 178847
(.leaf ⟨178828,19,(.group 6 1744 false)⟩)
(.leaf ⟨178847,19,(.group 6 1745 false)⟩))
(.branch 178885
(.leaf ⟨178866,19,(.group 6 1746 false)⟩)
(.leaf ⟨178885,19,(.group 6 1747 false)⟩)))
(.branch 178942
(.branch 178923
(.leaf ⟨178904,19,(.group 6 1748 false)⟩)
(.leaf ⟨178923,19,(.group 6 1749 false)⟩))
(.branch 178961
(.leaf ⟨178942,19,(.group 6 1750 false)⟩)
(.leaf ⟨178961,19,(.group 6 1751 false)⟩)))))
(.branch 179132
(.branch 179056
(.branch 179018
(.branch 178999
(.leaf ⟨178980,19,(.group 6 1752 false)⟩)
(.leaf ⟨178999,19,(.group 6 1753 false)⟩))
(.branch 179037
(.leaf ⟨179018,19,(.group 6 1754 false)⟩)
(.leaf ⟨179037,19,(.group 6 1755 false)⟩)))
(.branch 179094
(.branch 179075
(.leaf ⟨179056,19,(.group 6 1756 false)⟩)
(.leaf ⟨179075,19,(.group 6 1757 false)⟩))
(.branch 179113
(.leaf ⟨179094,19,(.group 6 1758 false)⟩)
(.leaf ⟨179113,19,(.group 6 1759 false)⟩))))
(.branch 179208
(.branch 179170
(.branch 179151
(.leaf ⟨179132,19,(.group 6 1760 false)⟩)
(.leaf ⟨179151,19,(.group 6 1761 false)⟩))
(.branch 179189
(.leaf ⟨179170,19,(.group 6 1762 false)⟩)
(.leaf ⟨179189,19,(.group 6 1763 false)⟩)))
(.branch 179246
(.branch 179227
(.leaf ⟨179208,19,(.group 6 1764 false)⟩)
(.leaf ⟨179227,19,(.group 6 1765 false)⟩))
(.branch 179265
(.leaf ⟨179246,19,(.group 6 1766 false)⟩)
(.leaf ⟨179265,19,(.group 6 1767 false)⟩)))))))

theorem tree172_checked : tree172.check 178068 179284 = true := by decide +kernel

def tree173 : Tree := (.branch 179892
(.branch 179588
(.branch 179436
(.branch 179360
(.branch 179322
(.branch 179303
(.leaf ⟨179284,19,(.group 6 1768 false)⟩)
(.leaf ⟨179303,19,(.group 6 1769 false)⟩))
(.branch 179341
(.leaf ⟨179322,19,(.group 6 1770 false)⟩)
(.leaf ⟨179341,19,(.group 6 1771 false)⟩)))
(.branch 179398
(.branch 179379
(.leaf ⟨179360,19,(.group 6 1772 false)⟩)
(.leaf ⟨179379,19,(.group 6 1773 false)⟩))
(.branch 179417
(.leaf ⟨179398,19,(.group 6 1774 false)⟩)
(.leaf ⟨179417,19,(.group 6 1775 false)⟩))))
(.branch 179512
(.branch 179474
(.branch 179455
(.leaf ⟨179436,19,(.group 6 1776 false)⟩)
(.leaf ⟨179455,19,(.group 6 1777 false)⟩))
(.branch 179493
(.leaf ⟨179474,19,(.group 6 1778 false)⟩)
(.leaf ⟨179493,19,(.group 6 1779 false)⟩)))
(.branch 179550
(.branch 179531
(.leaf ⟨179512,19,(.group 6 1780 false)⟩)
(.leaf ⟨179531,19,(.group 6 1781 false)⟩))
(.branch 179569
(.leaf ⟨179550,19,(.group 6 1782 false)⟩)
(.leaf ⟨179569,19,(.group 6 1783 false)⟩)))))
(.branch 179740
(.branch 179664
(.branch 179626
(.branch 179607
(.leaf ⟨179588,19,(.group 6 1784 false)⟩)
(.leaf ⟨179607,19,(.group 6 1785 false)⟩))
(.branch 179645
(.leaf ⟨179626,19,(.group 6 1786 false)⟩)
(.leaf ⟨179645,19,(.group 6 1787 false)⟩)))
(.branch 179702
(.branch 179683
(.leaf ⟨179664,19,(.group 6 1788 false)⟩)
(.leaf ⟨179683,19,(.group 6 1789 false)⟩))
(.branch 179721
(.leaf ⟨179702,19,(.group 6 1790 false)⟩)
(.leaf ⟨179721,19,(.group 6 1791 false)⟩))))
(.branch 179816
(.branch 179778
(.branch 179759
(.leaf ⟨179740,19,(.group 6 1792 false)⟩)
(.leaf ⟨179759,19,(.group 6 1793 false)⟩))
(.branch 179797
(.leaf ⟨179778,19,(.group 6 1794 false)⟩)
(.leaf ⟨179797,19,(.group 6 1795 false)⟩)))
(.branch 179854
(.branch 179835
(.leaf ⟨179816,19,(.group 6 1796 false)⟩)
(.leaf ⟨179835,19,(.group 6 1797 false)⟩))
(.branch 179873
(.leaf ⟨179854,19,(.group 6 1798 false)⟩)
(.leaf ⟨179873,19,(.group 6 1799 false)⟩))))))
(.branch 180196
(.branch 180044
(.branch 179968
(.branch 179930
(.branch 179911
(.leaf ⟨179892,19,(.group 6 1800 false)⟩)
(.leaf ⟨179911,19,(.group 6 1801 false)⟩))
(.branch 179949
(.leaf ⟨179930,19,(.group 6 1802 false)⟩)
(.leaf ⟨179949,19,(.group 6 1803 false)⟩)))
(.branch 180006
(.branch 179987
(.leaf ⟨179968,19,(.group 6 1804 false)⟩)
(.leaf ⟨179987,19,(.group 6 1805 false)⟩))
(.branch 180025
(.leaf ⟨180006,19,(.group 6 1806 false)⟩)
(.leaf ⟨180025,19,(.group 6 1807 false)⟩))))
(.branch 180120
(.branch 180082
(.branch 180063
(.leaf ⟨180044,19,(.group 6 1808 false)⟩)
(.leaf ⟨180063,19,(.group 6 1809 false)⟩))
(.branch 180101
(.leaf ⟨180082,19,(.group 6 1810 false)⟩)
(.leaf ⟨180101,19,(.group 6 1811 false)⟩)))
(.branch 180158
(.branch 180139
(.leaf ⟨180120,19,(.group 6 1812 false)⟩)
(.leaf ⟨180139,19,(.group 6 1813 false)⟩))
(.branch 180177
(.leaf ⟨180158,19,(.group 6 1814 false)⟩)
(.leaf ⟨180177,19,(.group 6 1815 false)⟩)))))
(.branch 180348
(.branch 180272
(.branch 180234
(.branch 180215
(.leaf ⟨180196,19,(.group 6 1816 false)⟩)
(.leaf ⟨180215,19,(.group 6 1817 false)⟩))
(.branch 180253
(.leaf ⟨180234,19,(.group 6 1818 false)⟩)
(.leaf ⟨180253,19,(.group 6 1819 false)⟩)))
(.branch 180310
(.branch 180291
(.leaf ⟨180272,19,(.group 6 1820 false)⟩)
(.leaf ⟨180291,19,(.group 6 1821 false)⟩))
(.branch 180329
(.leaf ⟨180310,19,(.group 6 1822 false)⟩)
(.leaf ⟨180329,19,(.group 6 1823 false)⟩))))
(.branch 180424
(.branch 180386
(.branch 180367
(.leaf ⟨180348,19,(.group 6 1824 false)⟩)
(.leaf ⟨180367,19,(.group 6 1825 false)⟩))
(.branch 180405
(.leaf ⟨180386,19,(.group 6 1826 false)⟩)
(.leaf ⟨180405,19,(.group 6 1827 false)⟩)))
(.branch 180462
(.branch 180443
(.leaf ⟨180424,19,(.group 6 1828 false)⟩)
(.leaf ⟨180443,19,(.group 6 1829 false)⟩))
(.branch 180481
(.leaf ⟨180462,19,(.group 6 1830 false)⟩)
(.leaf ⟨180481,19,(.group 6 1831 false)⟩)))))))

theorem tree173_checked : tree173.check 179284 180500 = true := by decide +kernel

def tree174 : Tree := (.branch 181108
(.branch 180804
(.branch 180652
(.branch 180576
(.branch 180538
(.branch 180519
(.leaf ⟨180500,19,(.group 6 1832 false)⟩)
(.leaf ⟨180519,19,(.group 6 1833 false)⟩))
(.branch 180557
(.leaf ⟨180538,19,(.group 6 1834 false)⟩)
(.leaf ⟨180557,19,(.group 6 1835 false)⟩)))
(.branch 180614
(.branch 180595
(.leaf ⟨180576,19,(.group 6 1836 false)⟩)
(.leaf ⟨180595,19,(.group 6 1837 false)⟩))
(.branch 180633
(.leaf ⟨180614,19,(.group 6 1838 false)⟩)
(.leaf ⟨180633,19,(.group 6 1839 false)⟩))))
(.branch 180728
(.branch 180690
(.branch 180671
(.leaf ⟨180652,19,(.group 6 1840 false)⟩)
(.leaf ⟨180671,19,(.group 6 1841 false)⟩))
(.branch 180709
(.leaf ⟨180690,19,(.group 6 1842 false)⟩)
(.leaf ⟨180709,19,(.group 6 1843 false)⟩)))
(.branch 180766
(.branch 180747
(.leaf ⟨180728,19,(.group 6 1844 false)⟩)
(.leaf ⟨180747,19,(.group 6 1845 false)⟩))
(.branch 180785
(.leaf ⟨180766,19,(.group 6 1846 false)⟩)
(.leaf ⟨180785,19,(.group 6 1847 false)⟩)))))
(.branch 180956
(.branch 180880
(.branch 180842
(.branch 180823
(.leaf ⟨180804,19,(.group 6 1848 false)⟩)
(.leaf ⟨180823,19,(.group 6 1849 false)⟩))
(.branch 180861
(.leaf ⟨180842,19,(.group 6 1850 false)⟩)
(.leaf ⟨180861,19,(.group 6 1851 false)⟩)))
(.branch 180918
(.branch 180899
(.leaf ⟨180880,19,(.group 6 1852 false)⟩)
(.leaf ⟨180899,19,(.group 6 1853 false)⟩))
(.branch 180937
(.leaf ⟨180918,19,(.group 6 1854 false)⟩)
(.leaf ⟨180937,19,(.group 6 1855 false)⟩))))
(.branch 181032
(.branch 180994
(.branch 180975
(.leaf ⟨180956,19,(.group 6 1856 false)⟩)
(.leaf ⟨180975,19,(.group 6 1857 false)⟩))
(.branch 181013
(.leaf ⟨180994,19,(.group 6 1858 false)⟩)
(.leaf ⟨181013,19,(.group 6 1859 false)⟩)))
(.branch 181070
(.branch 181051
(.leaf ⟨181032,19,(.group 6 1860 false)⟩)
(.leaf ⟨181051,19,(.group 6 1861 false)⟩))
(.branch 181089
(.leaf ⟨181070,19,(.group 6 1862 false)⟩)
(.leaf ⟨181089,19,(.group 6 1863 false)⟩))))))
(.branch 181412
(.branch 181260
(.branch 181184
(.branch 181146
(.branch 181127
(.leaf ⟨181108,19,(.group 6 1864 false)⟩)
(.leaf ⟨181127,19,(.group 6 1865 false)⟩))
(.branch 181165
(.leaf ⟨181146,19,(.group 6 1866 false)⟩)
(.leaf ⟨181165,19,(.group 6 1867 false)⟩)))
(.branch 181222
(.branch 181203
(.leaf ⟨181184,19,(.group 6 1868 false)⟩)
(.leaf ⟨181203,19,(.group 6 1869 false)⟩))
(.branch 181241
(.leaf ⟨181222,19,(.group 6 1870 false)⟩)
(.leaf ⟨181241,19,(.group 6 1871 false)⟩))))
(.branch 181336
(.branch 181298
(.branch 181279
(.leaf ⟨181260,19,(.group 6 1872 false)⟩)
(.leaf ⟨181279,19,(.group 6 1873 false)⟩))
(.branch 181317
(.leaf ⟨181298,19,(.group 6 1874 false)⟩)
(.leaf ⟨181317,19,(.group 6 1875 false)⟩)))
(.branch 181374
(.branch 181355
(.leaf ⟨181336,19,(.group 6 1876 false)⟩)
(.leaf ⟨181355,19,(.group 6 1877 false)⟩))
(.branch 181393
(.leaf ⟨181374,19,(.group 6 1878 false)⟩)
(.leaf ⟨181393,19,(.group 6 1879 false)⟩)))))
(.branch 181564
(.branch 181488
(.branch 181450
(.branch 181431
(.leaf ⟨181412,19,(.group 6 1880 false)⟩)
(.leaf ⟨181431,19,(.group 6 1881 false)⟩))
(.branch 181469
(.leaf ⟨181450,19,(.group 6 1882 false)⟩)
(.leaf ⟨181469,19,(.group 6 1883 false)⟩)))
(.branch 181526
(.branch 181507
(.leaf ⟨181488,19,(.group 6 1884 false)⟩)
(.leaf ⟨181507,19,(.group 6 1885 false)⟩))
(.branch 181545
(.leaf ⟨181526,19,(.group 6 1886 false)⟩)
(.leaf ⟨181545,19,(.group 6 1887 false)⟩))))
(.branch 181640
(.branch 181602
(.branch 181583
(.leaf ⟨181564,19,(.group 6 1888 false)⟩)
(.leaf ⟨181583,19,(.group 6 1889 false)⟩))
(.branch 181621
(.leaf ⟨181602,19,(.group 6 1890 false)⟩)
(.leaf ⟨181621,19,(.group 6 1891 false)⟩)))
(.branch 181678
(.branch 181659
(.leaf ⟨181640,19,(.group 6 1892 false)⟩)
(.leaf ⟨181659,19,(.group 6 1893 false)⟩))
(.branch 181697
(.leaf ⟨181678,19,(.group 6 1894 false)⟩)
(.leaf ⟨181697,19,(.group 6 1895 false)⟩)))))))

theorem tree174_checked : tree174.check 180500 181716 = true := by decide +kernel

def tree175 : Tree := (.branch 182324
(.branch 182020
(.branch 181868
(.branch 181792
(.branch 181754
(.branch 181735
(.leaf ⟨181716,19,(.group 6 1896 false)⟩)
(.leaf ⟨181735,19,(.group 6 1897 false)⟩))
(.branch 181773
(.leaf ⟨181754,19,(.group 6 1898 false)⟩)
(.leaf ⟨181773,19,(.group 6 1899 false)⟩)))
(.branch 181830
(.branch 181811
(.leaf ⟨181792,19,(.group 6 1900 false)⟩)
(.leaf ⟨181811,19,(.group 6 1901 false)⟩))
(.branch 181849
(.leaf ⟨181830,19,(.group 6 1902 false)⟩)
(.leaf ⟨181849,19,(.group 6 1903 false)⟩))))
(.branch 181944
(.branch 181906
(.branch 181887
(.leaf ⟨181868,19,(.group 6 1904 false)⟩)
(.leaf ⟨181887,19,(.group 6 1905 false)⟩))
(.branch 181925
(.leaf ⟨181906,19,(.group 6 1906 false)⟩)
(.leaf ⟨181925,19,(.group 6 1907 false)⟩)))
(.branch 181982
(.branch 181963
(.leaf ⟨181944,19,(.group 6 1908 false)⟩)
(.leaf ⟨181963,19,(.group 6 1909 false)⟩))
(.branch 182001
(.leaf ⟨181982,19,(.group 6 1910 false)⟩)
(.leaf ⟨182001,19,(.group 6 1911 false)⟩)))))
(.branch 182172
(.branch 182096
(.branch 182058
(.branch 182039
(.leaf ⟨182020,19,(.group 6 1912 false)⟩)
(.leaf ⟨182039,19,(.group 6 1913 false)⟩))
(.branch 182077
(.leaf ⟨182058,19,(.group 6 1914 false)⟩)
(.leaf ⟨182077,19,(.group 6 1915 false)⟩)))
(.branch 182134
(.branch 182115
(.leaf ⟨182096,19,(.group 6 1916 false)⟩)
(.leaf ⟨182115,19,(.group 6 1917 false)⟩))
(.branch 182153
(.leaf ⟨182134,19,(.group 6 1918 false)⟩)
(.leaf ⟨182153,19,(.group 6 1919 false)⟩))))
(.branch 182248
(.branch 182210
(.branch 182191
(.leaf ⟨182172,19,(.group 6 1920 false)⟩)
(.leaf ⟨182191,19,(.group 6 1921 false)⟩))
(.branch 182229
(.leaf ⟨182210,19,(.group 6 1922 false)⟩)
(.leaf ⟨182229,19,(.group 6 1923 false)⟩)))
(.branch 182286
(.branch 182267
(.leaf ⟨182248,19,(.group 6 1924 false)⟩)
(.leaf ⟨182267,19,(.group 6 1925 false)⟩))
(.branch 182305
(.leaf ⟨182286,19,(.group 6 1926 false)⟩)
(.leaf ⟨182305,19,(.group 6 1927 false)⟩))))))
(.branch 182628
(.branch 182476
(.branch 182400
(.branch 182362
(.branch 182343
(.leaf ⟨182324,19,(.group 6 1928 false)⟩)
(.leaf ⟨182343,19,(.group 6 1929 false)⟩))
(.branch 182381
(.leaf ⟨182362,19,(.group 6 1930 false)⟩)
(.leaf ⟨182381,19,(.group 6 1931 false)⟩)))
(.branch 182438
(.branch 182419
(.leaf ⟨182400,19,(.group 6 1932 false)⟩)
(.leaf ⟨182419,19,(.group 6 1933 false)⟩))
(.branch 182457
(.leaf ⟨182438,19,(.group 6 1934 false)⟩)
(.leaf ⟨182457,19,(.group 6 1935 false)⟩))))
(.branch 182552
(.branch 182514
(.branch 182495
(.leaf ⟨182476,19,(.group 6 1936 false)⟩)
(.leaf ⟨182495,19,(.group 6 1937 false)⟩))
(.branch 182533
(.leaf ⟨182514,19,(.group 6 1938 false)⟩)
(.leaf ⟨182533,19,(.group 6 1939 false)⟩)))
(.branch 182590
(.branch 182571
(.leaf ⟨182552,19,(.group 6 1940 false)⟩)
(.leaf ⟨182571,19,(.group 6 1941 false)⟩))
(.branch 182609
(.leaf ⟨182590,19,(.group 6 1942 false)⟩)
(.leaf ⟨182609,19,(.group 6 1943 false)⟩)))))
(.branch 182780
(.branch 182704
(.branch 182666
(.branch 182647
(.leaf ⟨182628,19,(.group 6 1944 false)⟩)
(.leaf ⟨182647,19,(.group 6 1945 false)⟩))
(.branch 182685
(.leaf ⟨182666,19,(.group 6 1946 false)⟩)
(.leaf ⟨182685,19,(.group 6 1947 false)⟩)))
(.branch 182742
(.branch 182723
(.leaf ⟨182704,19,(.group 6 1948 false)⟩)
(.leaf ⟨182723,19,(.group 6 1949 false)⟩))
(.branch 182761
(.leaf ⟨182742,19,(.group 6 1950 false)⟩)
(.leaf ⟨182761,19,(.group 6 1951 false)⟩))))
(.branch 182856
(.branch 182818
(.branch 182799
(.leaf ⟨182780,19,(.group 6 1952 false)⟩)
(.leaf ⟨182799,19,(.group 6 1953 false)⟩))
(.branch 182837
(.leaf ⟨182818,19,(.group 6 1954 false)⟩)
(.leaf ⟨182837,19,(.group 6 1955 false)⟩)))
(.branch 182894
(.branch 182875
(.leaf ⟨182856,19,(.group 6 1956 false)⟩)
(.leaf ⟨182875,19,(.group 6 1957 false)⟩))
(.branch 182913
(.leaf ⟨182894,19,(.group 6 1958 false)⟩)
(.leaf ⟨182913,19,(.group 6 1959 false)⟩)))))))

theorem tree175_checked : tree175.check 181716 182932 = true := by decide +kernel

def tree176 : Tree := (.branch 183540
(.branch 183236
(.branch 183084
(.branch 183008
(.branch 182970
(.branch 182951
(.leaf ⟨182932,19,(.group 6 1960 false)⟩)
(.leaf ⟨182951,19,(.group 6 1961 false)⟩))
(.branch 182989
(.leaf ⟨182970,19,(.group 6 1962 false)⟩)
(.leaf ⟨182989,19,(.group 6 1963 false)⟩)))
(.branch 183046
(.branch 183027
(.leaf ⟨183008,19,(.group 6 1964 false)⟩)
(.leaf ⟨183027,19,(.group 6 1965 false)⟩))
(.branch 183065
(.leaf ⟨183046,19,(.group 6 1966 false)⟩)
(.leaf ⟨183065,19,(.group 6 1967 false)⟩))))
(.branch 183160
(.branch 183122
(.branch 183103
(.leaf ⟨183084,19,(.group 6 1968 false)⟩)
(.leaf ⟨183103,19,(.group 6 1969 false)⟩))
(.branch 183141
(.leaf ⟨183122,19,(.group 6 1970 false)⟩)
(.leaf ⟨183141,19,(.group 6 1971 false)⟩)))
(.branch 183198
(.branch 183179
(.leaf ⟨183160,19,(.group 6 1972 false)⟩)
(.leaf ⟨183179,19,(.group 6 1973 false)⟩))
(.branch 183217
(.leaf ⟨183198,19,(.group 6 1974 false)⟩)
(.leaf ⟨183217,19,(.group 6 1975 false)⟩)))))
(.branch 183388
(.branch 183312
(.branch 183274
(.branch 183255
(.leaf ⟨183236,19,(.group 6 1976 false)⟩)
(.leaf ⟨183255,19,(.group 6 1977 false)⟩))
(.branch 183293
(.leaf ⟨183274,19,(.group 6 1978 false)⟩)
(.leaf ⟨183293,19,(.group 6 1979 false)⟩)))
(.branch 183350
(.branch 183331
(.leaf ⟨183312,19,(.group 6 1980 false)⟩)
(.leaf ⟨183331,19,(.group 6 1981 false)⟩))
(.branch 183369
(.leaf ⟨183350,19,(.group 6 1982 false)⟩)
(.leaf ⟨183369,19,(.group 6 1983 false)⟩))))
(.branch 183464
(.branch 183426
(.branch 183407
(.leaf ⟨183388,19,(.group 6 1984 false)⟩)
(.leaf ⟨183407,19,(.group 6 1985 false)⟩))
(.branch 183445
(.leaf ⟨183426,19,(.group 6 1986 false)⟩)
(.leaf ⟨183445,19,(.group 6 1987 false)⟩)))
(.branch 183502
(.branch 183483
(.leaf ⟨183464,19,(.group 6 1988 false)⟩)
(.leaf ⟨183483,19,(.group 6 1989 false)⟩))
(.branch 183521
(.leaf ⟨183502,19,(.group 6 1990 false)⟩)
(.leaf ⟨183521,19,(.group 6 1991 false)⟩))))))
(.branch 183844
(.branch 183692
(.branch 183616
(.branch 183578
(.branch 183559
(.leaf ⟨183540,19,(.group 6 1992 false)⟩)
(.leaf ⟨183559,19,(.group 6 1993 false)⟩))
(.branch 183597
(.leaf ⟨183578,19,(.group 6 1994 false)⟩)
(.leaf ⟨183597,19,(.group 6 1995 false)⟩)))
(.branch 183654
(.branch 183635
(.leaf ⟨183616,19,(.group 6 1996 false)⟩)
(.leaf ⟨183635,19,(.group 6 1997 false)⟩))
(.branch 183673
(.leaf ⟨183654,19,(.group 6 1998 false)⟩)
(.leaf ⟨183673,19,(.group 6 1999 false)⟩))))
(.branch 183768
(.branch 183730
(.branch 183711
(.leaf ⟨183692,19,(.group 6 2000 false)⟩)
(.leaf ⟨183711,19,(.group 6 2001 false)⟩))
(.branch 183749
(.leaf ⟨183730,19,(.group 6 2002 false)⟩)
(.leaf ⟨183749,19,(.group 6 2003 false)⟩)))
(.branch 183806
(.branch 183787
(.leaf ⟨183768,19,(.group 6 2004 false)⟩)
(.leaf ⟨183787,19,(.group 6 2005 false)⟩))
(.branch 183825
(.leaf ⟨183806,19,(.group 6 2006 false)⟩)
(.leaf ⟨183825,19,(.group 6 2007 false)⟩)))))
(.branch 183996
(.branch 183920
(.branch 183882
(.branch 183863
(.leaf ⟨183844,19,(.group 6 2008 false)⟩)
(.leaf ⟨183863,19,(.group 6 2009 false)⟩))
(.branch 183901
(.leaf ⟨183882,19,(.group 6 2010 false)⟩)
(.leaf ⟨183901,19,(.group 6 2011 false)⟩)))
(.branch 183958
(.branch 183939
(.leaf ⟨183920,19,(.group 6 2012 false)⟩)
(.leaf ⟨183939,19,(.group 6 2013 false)⟩))
(.branch 183977
(.leaf ⟨183958,19,(.group 6 2014 false)⟩)
(.leaf ⟨183977,19,(.group 6 2015 false)⟩))))
(.branch 184072
(.branch 184034
(.branch 184015
(.leaf ⟨183996,19,(.group 6 2016 false)⟩)
(.leaf ⟨184015,19,(.group 6 2017 false)⟩))
(.branch 184053
(.leaf ⟨184034,19,(.group 6 2018 false)⟩)
(.leaf ⟨184053,19,(.group 6 2019 false)⟩)))
(.branch 184110
(.branch 184091
(.leaf ⟨184072,19,(.group 6 2020 false)⟩)
(.leaf ⟨184091,19,(.group 6 2021 false)⟩))
(.branch 184129
(.leaf ⟨184110,19,(.group 6 2022 false)⟩)
(.leaf ⟨184129,19,(.group 6 2023 false)⟩)))))))

theorem tree176_checked : tree176.check 182932 184148 = true := by decide +kernel

def tree177 : Tree := (.branch 184756
(.branch 184452
(.branch 184300
(.branch 184224
(.branch 184186
(.branch 184167
(.leaf ⟨184148,19,(.group 6 2024 false)⟩)
(.leaf ⟨184167,19,(.group 6 2025 false)⟩))
(.branch 184205
(.leaf ⟨184186,19,(.group 6 2026 false)⟩)
(.leaf ⟨184205,19,(.group 6 2027 false)⟩)))
(.branch 184262
(.branch 184243
(.leaf ⟨184224,19,(.group 6 2028 false)⟩)
(.leaf ⟨184243,19,(.group 6 2029 false)⟩))
(.branch 184281
(.leaf ⟨184262,19,(.group 6 2030 false)⟩)
(.leaf ⟨184281,19,(.group 6 2031 false)⟩))))
(.branch 184376
(.branch 184338
(.branch 184319
(.leaf ⟨184300,19,(.group 6 2032 false)⟩)
(.leaf ⟨184319,19,(.group 6 2033 false)⟩))
(.branch 184357
(.leaf ⟨184338,19,(.group 6 2034 false)⟩)
(.leaf ⟨184357,19,(.group 6 2035 false)⟩)))
(.branch 184414
(.branch 184395
(.leaf ⟨184376,19,(.group 6 2036 false)⟩)
(.leaf ⟨184395,19,(.group 6 2037 false)⟩))
(.branch 184433
(.leaf ⟨184414,19,(.group 6 2038 false)⟩)
(.leaf ⟨184433,19,(.group 6 2039 false)⟩)))))
(.branch 184604
(.branch 184528
(.branch 184490
(.branch 184471
(.leaf ⟨184452,19,(.group 6 2040 false)⟩)
(.leaf ⟨184471,19,(.group 6 2041 false)⟩))
(.branch 184509
(.leaf ⟨184490,19,(.group 6 2042 false)⟩)
(.leaf ⟨184509,19,(.group 6 2043 false)⟩)))
(.branch 184566
(.branch 184547
(.leaf ⟨184528,19,(.group 6 2044 false)⟩)
(.leaf ⟨184547,19,(.group 6 2045 false)⟩))
(.branch 184585
(.leaf ⟨184566,19,(.group 6 2046 false)⟩)
(.leaf ⟨184585,19,(.group 6 2047 false)⟩))))
(.branch 184680
(.branch 184642
(.branch 184623
(.leaf ⟨184604,19,(.group 7 397 false)⟩)
(.leaf ⟨184623,19,(.group 7 398 false)⟩))
(.branch 184661
(.leaf ⟨184642,19,(.group 7 399 false)⟩)
(.leaf ⟨184661,19,(.group 7 400 false)⟩)))
(.branch 184718
(.branch 184699
(.leaf ⟨184680,19,(.group 7 401 false)⟩)
(.leaf ⟨184699,19,(.group 7 402 false)⟩))
(.branch 184737
(.leaf ⟨184718,19,(.group 7 403 false)⟩)
(.leaf ⟨184737,19,(.group 7 404 false)⟩))))))
(.branch 185060
(.branch 184908
(.branch 184832
(.branch 184794
(.branch 184775
(.leaf ⟨184756,19,(.group 7 405 false)⟩)
(.leaf ⟨184775,19,(.group 7 406 false)⟩))
(.branch 184813
(.leaf ⟨184794,19,(.group 7 407 false)⟩)
(.leaf ⟨184813,19,(.group 7 408 false)⟩)))
(.branch 184870
(.branch 184851
(.leaf ⟨184832,19,(.group 7 409 false)⟩)
(.leaf ⟨184851,19,(.group 7 410 false)⟩))
(.branch 184889
(.leaf ⟨184870,19,(.group 7 411 false)⟩)
(.leaf ⟨184889,19,(.group 7 412 false)⟩))))
(.branch 184984
(.branch 184946
(.branch 184927
(.leaf ⟨184908,19,(.group 7 413 false)⟩)
(.leaf ⟨184927,19,(.group 7 414 false)⟩))
(.branch 184965
(.leaf ⟨184946,19,(.group 7 415 false)⟩)
(.leaf ⟨184965,19,(.group 7 416 false)⟩)))
(.branch 185022
(.branch 185003
(.leaf ⟨184984,19,(.group 7 417 false)⟩)
(.leaf ⟨185003,19,(.group 7 418 false)⟩))
(.branch 185041
(.leaf ⟨185022,19,(.group 7 419 false)⟩)
(.leaf ⟨185041,19,(.group 7 420 false)⟩)))))
(.branch 185212
(.branch 185136
(.branch 185098
(.branch 185079
(.leaf ⟨185060,19,(.group 7 421 false)⟩)
(.leaf ⟨185079,19,(.group 7 422 false)⟩))
(.branch 185117
(.leaf ⟨185098,19,(.group 7 423 false)⟩)
(.leaf ⟨185117,19,(.group 7 424 false)⟩)))
(.branch 185174
(.branch 185155
(.leaf ⟨185136,19,(.group 7 425 false)⟩)
(.leaf ⟨185155,19,(.group 7 426 false)⟩))
(.branch 185193
(.leaf ⟨185174,19,(.group 7 427 false)⟩)
(.leaf ⟨185193,19,(.group 7 428 false)⟩))))
(.branch 185288
(.branch 185250
(.branch 185231
(.leaf ⟨185212,19,(.group 7 429 false)⟩)
(.leaf ⟨185231,19,(.group 7 430 false)⟩))
(.branch 185269
(.leaf ⟨185250,19,(.group 7 431 false)⟩)
(.leaf ⟨185269,19,(.group 7 432 false)⟩)))
(.branch 185326
(.branch 185307
(.leaf ⟨185288,19,(.group 7 433 false)⟩)
(.leaf ⟨185307,19,(.group 7 434 false)⟩))
(.branch 185345
(.leaf ⟨185326,19,(.group 7 435 false)⟩)
(.leaf ⟨185345,19,(.group 7 436 false)⟩)))))))

theorem tree177_checked : tree177.check 184148 185364 = true := by decide +kernel

def tree178 : Tree := (.branch 185972
(.branch 185668
(.branch 185516
(.branch 185440
(.branch 185402
(.branch 185383
(.leaf ⟨185364,19,(.group 7 437 false)⟩)
(.leaf ⟨185383,19,(.group 7 438 false)⟩))
(.branch 185421
(.leaf ⟨185402,19,(.group 7 439 false)⟩)
(.leaf ⟨185421,19,(.group 7 440 false)⟩)))
(.branch 185478
(.branch 185459
(.leaf ⟨185440,19,(.group 7 441 false)⟩)
(.leaf ⟨185459,19,(.group 7 442 false)⟩))
(.branch 185497
(.leaf ⟨185478,19,(.group 7 443 false)⟩)
(.leaf ⟨185497,19,(.group 7 444 false)⟩))))
(.branch 185592
(.branch 185554
(.branch 185535
(.leaf ⟨185516,19,(.group 7 445 false)⟩)
(.leaf ⟨185535,19,(.group 7 446 false)⟩))
(.branch 185573
(.leaf ⟨185554,19,(.group 7 447 false)⟩)
(.leaf ⟨185573,19,(.group 7 448 false)⟩)))
(.branch 185630
(.branch 185611
(.leaf ⟨185592,19,(.group 7 449 false)⟩)
(.leaf ⟨185611,19,(.group 7 450 false)⟩))
(.branch 185649
(.leaf ⟨185630,19,(.group 7 451 false)⟩)
(.leaf ⟨185649,19,(.group 7 452 false)⟩)))))
(.branch 185820
(.branch 185744
(.branch 185706
(.branch 185687
(.leaf ⟨185668,19,(.group 7 453 false)⟩)
(.leaf ⟨185687,19,(.group 7 454 false)⟩))
(.branch 185725
(.leaf ⟨185706,19,(.group 7 455 false)⟩)
(.leaf ⟨185725,19,(.group 7 456 false)⟩)))
(.branch 185782
(.branch 185763
(.leaf ⟨185744,19,(.group 7 457 false)⟩)
(.leaf ⟨185763,19,(.group 7 458 false)⟩))
(.branch 185801
(.leaf ⟨185782,19,(.group 7 459 false)⟩)
(.leaf ⟨185801,19,(.group 7 460 false)⟩))))
(.branch 185896
(.branch 185858
(.branch 185839
(.leaf ⟨185820,19,(.group 7 461 false)⟩)
(.leaf ⟨185839,19,(.group 7 462 false)⟩))
(.branch 185877
(.leaf ⟨185858,19,(.group 7 463 false)⟩)
(.leaf ⟨185877,19,(.group 7 464 false)⟩)))
(.branch 185934
(.branch 185915
(.leaf ⟨185896,19,(.group 7 465 false)⟩)
(.leaf ⟨185915,19,(.group 7 466 false)⟩))
(.branch 185953
(.leaf ⟨185934,19,(.group 7 467 false)⟩)
(.leaf ⟨185953,19,(.group 7 468 false)⟩))))))
(.branch 186276
(.branch 186124
(.branch 186048
(.branch 186010
(.branch 185991
(.leaf ⟨185972,19,(.group 7 469 false)⟩)
(.leaf ⟨185991,19,(.group 7 470 false)⟩))
(.branch 186029
(.leaf ⟨186010,19,(.group 7 471 false)⟩)
(.leaf ⟨186029,19,(.group 7 472 false)⟩)))
(.branch 186086
(.branch 186067
(.leaf ⟨186048,19,(.group 7 473 false)⟩)
(.leaf ⟨186067,19,(.group 7 474 false)⟩))
(.branch 186105
(.leaf ⟨186086,19,(.group 7 475 false)⟩)
(.leaf ⟨186105,19,(.group 7 476 false)⟩))))
(.branch 186200
(.branch 186162
(.branch 186143
(.leaf ⟨186124,19,(.group 7 477 false)⟩)
(.leaf ⟨186143,19,(.group 7 478 false)⟩))
(.branch 186181
(.leaf ⟨186162,19,(.group 7 479 false)⟩)
(.leaf ⟨186181,19,(.group 7 480 false)⟩)))
(.branch 186238
(.branch 186219
(.leaf ⟨186200,19,(.group 7 481 false)⟩)
(.leaf ⟨186219,19,(.group 7 482 false)⟩))
(.branch 186257
(.leaf ⟨186238,19,(.group 7 483 false)⟩)
(.leaf ⟨186257,19,(.group 7 484 false)⟩)))))
(.branch 186428
(.branch 186352
(.branch 186314
(.branch 186295
(.leaf ⟨186276,19,(.group 7 485 false)⟩)
(.leaf ⟨186295,19,(.group 7 486 false)⟩))
(.branch 186333
(.leaf ⟨186314,19,(.group 7 487 false)⟩)
(.leaf ⟨186333,19,(.group 8 495 false)⟩)))
(.branch 186390
(.branch 186371
(.leaf ⟨186352,19,(.group 8 496 false)⟩)
(.leaf ⟨186371,19,(.group 8 497 false)⟩))
(.branch 186409
(.leaf ⟨186390,19,(.group 8 498 false)⟩)
(.leaf ⟨186409,19,(.group 8 499 false)⟩))))
(.branch 186504
(.branch 186466
(.branch 186447
(.leaf ⟨186428,19,(.group 8 500 false)⟩)
(.leaf ⟨186447,19,(.group 8 501 false)⟩))
(.branch 186485
(.leaf ⟨186466,19,(.group 8 502 false)⟩)
(.leaf ⟨186485,19,(.group 8 503 false)⟩)))
(.branch 186542
(.branch 186523
(.leaf ⟨186504,19,(.group 8 504 false)⟩)
(.leaf ⟨186523,19,(.group 8 505 false)⟩))
(.branch 186561
(.leaf ⟨186542,19,(.group 8 506 false)⟩)
(.leaf ⟨186561,19,(.group 8 507 false)⟩)))))))

theorem tree178_checked : tree178.check 185364 186580 = true := by decide +kernel

def tree179 : Tree := (.branch 187188
(.branch 186884
(.branch 186732
(.branch 186656
(.branch 186618
(.branch 186599
(.leaf ⟨186580,19,(.group 8 508 false)⟩)
(.leaf ⟨186599,19,(.group 8 509 false)⟩))
(.branch 186637
(.leaf ⟨186618,19,(.group 8 510 false)⟩)
(.leaf ⟨186637,19,(.group 8 511 false)⟩)))
(.branch 186694
(.branch 186675
(.leaf ⟨186656,19,(.group 8 512 false)⟩)
(.leaf ⟨186675,19,(.group 8 513 false)⟩))
(.branch 186713
(.leaf ⟨186694,19,(.group 8 514 false)⟩)
(.leaf ⟨186713,19,(.group 8 515 false)⟩))))
(.branch 186808
(.branch 186770
(.branch 186751
(.leaf ⟨186732,19,(.group 8 516 false)⟩)
(.leaf ⟨186751,19,(.group 8 517 false)⟩))
(.branch 186789
(.leaf ⟨186770,19,(.group 8 518 false)⟩)
(.leaf ⟨186789,19,(.group 8 519 false)⟩)))
(.branch 186846
(.branch 186827
(.leaf ⟨186808,19,(.group 8 520 false)⟩)
(.leaf ⟨186827,19,(.group 8 521 false)⟩))
(.branch 186865
(.leaf ⟨186846,19,(.group 8 522 false)⟩)
(.leaf ⟨186865,19,(.group 8 523 false)⟩)))))
(.branch 187036
(.branch 186960
(.branch 186922
(.branch 186903
(.leaf ⟨186884,19,(.group 8 524 false)⟩)
(.leaf ⟨186903,19,(.group 8 525 false)⟩))
(.branch 186941
(.leaf ⟨186922,19,(.group 8 526 false)⟩)
(.leaf ⟨186941,19,(.group 8 527 false)⟩)))
(.branch 186998
(.branch 186979
(.leaf ⟨186960,19,(.group 8 528 false)⟩)
(.leaf ⟨186979,19,(.group 8 529 false)⟩))
(.branch 187017
(.leaf ⟨186998,19,(.group 8 530 false)⟩)
(.leaf ⟨187017,19,(.group 8 531 false)⟩))))
(.branch 187112
(.branch 187074
(.branch 187055
(.leaf ⟨187036,19,(.group 8 532 false)⟩)
(.leaf ⟨187055,19,(.group 8 533 false)⟩))
(.branch 187093
(.leaf ⟨187074,19,(.group 8 534 false)⟩)
(.leaf ⟨187093,19,(.group 8 535 false)⟩)))
(.branch 187150
(.branch 187131
(.leaf ⟨187112,19,(.group 8 536 false)⟩)
(.leaf ⟨187131,19,(.group 8 537 false)⟩))
(.branch 187169
(.leaf ⟨187150,19,(.group 8 538 false)⟩)
(.leaf ⟨187169,19,(.group 8 539 false)⟩))))))
(.branch 187505
(.branch 187345
(.branch 187265
(.branch 187226
(.branch 187207
(.leaf ⟨187188,19,(.group 8 540 false)⟩)
(.leaf ⟨187207,19,(.group 8 541 false)⟩))
(.branch 187245
(.leaf ⟨187226,19,(.group 8 542 false)⟩)
(.leaf ⟨187245,20,(.group 1 455 false)⟩)))
(.branch 187305
(.branch 187285
(.leaf ⟨187265,20,(.group 1 456 false)⟩)
(.leaf ⟨187285,20,(.group 1 457 false)⟩))
(.branch 187325
(.leaf ⟨187305,20,(.group 1 458 false)⟩)
(.leaf ⟨187325,20,(.group 1 459 false)⟩))))
(.branch 187425
(.branch 187385
(.branch 187365
(.leaf ⟨187345,20,(.group 1 460 false)⟩)
(.leaf ⟨187365,20,(.group 1 461 false)⟩))
(.branch 187405
(.leaf ⟨187385,20,(.group 1 462 false)⟩)
(.leaf ⟨187405,20,(.group 1 463 false)⟩)))
(.branch 187465
(.branch 187445
(.leaf ⟨187425,20,(.group 1 464 false)⟩)
(.leaf ⟨187445,20,(.group 1 465 false)⟩))
(.branch 187485
(.leaf ⟨187465,20,(.group 1 466 false)⟩)
(.leaf ⟨187485,20,(.group 1 467 false)⟩)))))
(.branch 187665
(.branch 187585
(.branch 187545
(.branch 187525
(.leaf ⟨187505,20,(.group 1 468 false)⟩)
(.leaf ⟨187525,20,(.group 1 469 false)⟩))
(.branch 187565
(.leaf ⟨187545,20,(.group 1 470 false)⟩)
(.leaf ⟨187565,20,(.group 1 471 false)⟩)))
(.branch 187625
(.branch 187605
(.leaf ⟨187585,20,(.group 1 472 false)⟩)
(.leaf ⟨187605,20,(.group 1 473 false)⟩))
(.branch 187645
(.leaf ⟨187625,20,(.group 1 474 false)⟩)
(.leaf ⟨187645,20,(.group 1 475 false)⟩))))
(.branch 187745
(.branch 187705
(.branch 187685
(.leaf ⟨187665,20,(.group 1 476 false)⟩)
(.leaf ⟨187685,20,(.group 1 477 false)⟩))
(.branch 187725
(.leaf ⟨187705,20,(.group 1 478 false)⟩)
(.leaf ⟨187725,20,(.group 1 479 false)⟩)))
(.branch 187785
(.branch 187765
(.leaf ⟨187745,20,(.group 1 480 false)⟩)
(.leaf ⟨187765,20,(.group 1 481 false)⟩))
(.branch 187805
(.leaf ⟨187785,20,(.group 1 482 false)⟩)
(.leaf ⟨187805,20,(.group 1 483 false)⟩)))))))

theorem tree179_checked : tree179.check 186580 187825 = true := by decide +kernel

def tree180 : Tree := (.branch 188465
(.branch 188145
(.branch 187985
(.branch 187905
(.branch 187865
(.branch 187845
(.leaf ⟨187825,20,(.group 1 484 false)⟩)
(.leaf ⟨187845,20,(.group 1 485 false)⟩))
(.branch 187885
(.leaf ⟨187865,20,(.group 1 486 false)⟩)
(.leaf ⟨187885,20,(.group 1 487 false)⟩)))
(.branch 187945
(.branch 187925
(.leaf ⟨187905,20,(.group 1 488 false)⟩)
(.leaf ⟨187925,20,(.group 1 489 false)⟩))
(.branch 187965
(.leaf ⟨187945,20,(.group 1 490 false)⟩)
(.leaf ⟨187965,20,(.group 1 491 false)⟩))))
(.branch 188065
(.branch 188025
(.branch 188005
(.leaf ⟨187985,20,(.group 1 492 false)⟩)
(.leaf ⟨188005,20,(.group 1 493 false)⟩))
(.branch 188045
(.leaf ⟨188025,20,(.group 1 494 false)⟩)
(.leaf ⟨188045,20,(.group 1 495 false)⟩)))
(.branch 188105
(.branch 188085
(.leaf ⟨188065,20,(.group 1 496 false)⟩)
(.leaf ⟨188085,20,(.group 1 497 false)⟩))
(.branch 188125
(.leaf ⟨188105,20,(.group 1 498 false)⟩)
(.leaf ⟨188125,20,(.group 1 499 false)⟩)))))
(.branch 188305
(.branch 188225
(.branch 188185
(.branch 188165
(.leaf ⟨188145,20,(.group 1 500 false)⟩)
(.leaf ⟨188165,20,(.group 1 501 false)⟩))
(.branch 188205
(.leaf ⟨188185,20,(.group 1 502 false)⟩)
(.leaf ⟨188205,20,(.group 1 503 false)⟩)))
(.branch 188265
(.branch 188245
(.leaf ⟨188225,20,(.group 1 504 false)⟩)
(.leaf ⟨188245,20,(.group 1 505 false)⟩))
(.branch 188285
(.leaf ⟨188265,20,(.group 1 506 false)⟩)
(.leaf ⟨188285,20,(.group 1 507 false)⟩))))
(.branch 188385
(.branch 188345
(.branch 188325
(.leaf ⟨188305,20,(.group 1 508 false)⟩)
(.leaf ⟨188325,20,(.group 1 509 false)⟩))
(.branch 188365
(.leaf ⟨188345,20,(.group 1 510 false)⟩)
(.leaf ⟨188365,20,(.group 1 511 false)⟩)))
(.branch 188425
(.branch 188405
(.leaf ⟨188385,20,(.group 2 455 false)⟩)
(.leaf ⟨188405,20,(.group 2 456 false)⟩))
(.branch 188445
(.leaf ⟨188425,20,(.group 2 457 false)⟩)
(.leaf ⟨188445,20,(.group 2 458 false)⟩))))))
(.branch 188785
(.branch 188625
(.branch 188545
(.branch 188505
(.branch 188485
(.leaf ⟨188465,20,(.group 2 459 false)⟩)
(.leaf ⟨188485,20,(.group 2 460 false)⟩))
(.branch 188525
(.leaf ⟨188505,20,(.group 2 461 false)⟩)
(.leaf ⟨188525,20,(.group 2 462 false)⟩)))
(.branch 188585
(.branch 188565
(.leaf ⟨188545,20,(.group 2 463 false)⟩)
(.leaf ⟨188565,20,(.group 2 464 false)⟩))
(.branch 188605
(.leaf ⟨188585,20,(.group 2 465 false)⟩)
(.leaf ⟨188605,20,(.group 2 466 false)⟩))))
(.branch 188705
(.branch 188665
(.branch 188645
(.leaf ⟨188625,20,(.group 2 467 false)⟩)
(.leaf ⟨188645,20,(.group 2 468 false)⟩))
(.branch 188685
(.leaf ⟨188665,20,(.group 2 469 false)⟩)
(.leaf ⟨188685,20,(.group 2 470 false)⟩)))
(.branch 188745
(.branch 188725
(.leaf ⟨188705,20,(.group 2 471 false)⟩)
(.leaf ⟨188725,20,(.group 2 472 false)⟩))
(.branch 188765
(.leaf ⟨188745,20,(.group 2 473 false)⟩)
(.leaf ⟨188765,20,(.group 2 474 false)⟩)))))
(.branch 188945
(.branch 188865
(.branch 188825
(.branch 188805
(.leaf ⟨188785,20,(.group 2 475 false)⟩)
(.leaf ⟨188805,20,(.group 2 476 false)⟩))
(.branch 188845
(.leaf ⟨188825,20,(.group 2 477 false)⟩)
(.leaf ⟨188845,20,(.group 2 478 false)⟩)))
(.branch 188905
(.branch 188885
(.leaf ⟨188865,20,(.group 2 479 false)⟩)
(.leaf ⟨188885,20,(.group 2 480 false)⟩))
(.branch 188925
(.leaf ⟨188905,20,(.group 2 481 false)⟩)
(.leaf ⟨188925,20,(.group 2 482 false)⟩))))
(.branch 189025
(.branch 188985
(.branch 188965
(.leaf ⟨188945,20,(.group 2 483 false)⟩)
(.leaf ⟨188965,20,(.group 2 484 false)⟩))
(.branch 189005
(.leaf ⟨188985,20,(.group 2 485 false)⟩)
(.leaf ⟨189005,20,(.group 2 486 false)⟩)))
(.branch 189065
(.branch 189045
(.leaf ⟨189025,20,(.group 2 487 false)⟩)
(.leaf ⟨189045,20,(.group 2 488 false)⟩))
(.branch 189085
(.leaf ⟨189065,20,(.group 2 489 false)⟩)
(.leaf ⟨189085,20,(.group 2 490 false)⟩)))))))

theorem tree180_checked : tree180.check 187825 189105 = true := by decide +kernel

def tree181 : Tree := (.branch 189745
(.branch 189425
(.branch 189265
(.branch 189185
(.branch 189145
(.branch 189125
(.leaf ⟨189105,20,(.group 2 491 false)⟩)
(.leaf ⟨189125,20,(.group 2 492 false)⟩))
(.branch 189165
(.leaf ⟨189145,20,(.group 2 493 false)⟩)
(.leaf ⟨189165,20,(.group 2 494 false)⟩)))
(.branch 189225
(.branch 189205
(.leaf ⟨189185,20,(.group 2 495 false)⟩)
(.leaf ⟨189205,20,(.group 2 496 false)⟩))
(.branch 189245
(.leaf ⟨189225,20,(.group 2 497 false)⟩)
(.leaf ⟨189245,20,(.group 2 498 false)⟩))))
(.branch 189345
(.branch 189305
(.branch 189285
(.leaf ⟨189265,20,(.group 2 499 false)⟩)
(.leaf ⟨189285,20,(.group 2 500 false)⟩))
(.branch 189325
(.leaf ⟨189305,20,(.group 2 501 false)⟩)
(.leaf ⟨189325,20,(.group 2 502 false)⟩)))
(.branch 189385
(.branch 189365
(.leaf ⟨189345,20,(.group 2 503 false)⟩)
(.leaf ⟨189365,20,(.group 2 504 false)⟩))
(.branch 189405
(.leaf ⟨189385,20,(.group 2 505 false)⟩)
(.leaf ⟨189405,20,(.group 2 506 false)⟩)))))
(.branch 189585
(.branch 189505
(.branch 189465
(.branch 189445
(.leaf ⟨189425,20,(.group 2 507 false)⟩)
(.leaf ⟨189445,20,(.group 2 508 false)⟩))
(.branch 189485
(.leaf ⟨189465,20,(.group 2 509 false)⟩)
(.leaf ⟨189485,20,(.group 2 510 false)⟩)))
(.branch 189545
(.branch 189525
(.leaf ⟨189505,20,(.group 2 511 false)⟩)
(.leaf ⟨189525,20,(.group 3 455 false)⟩))
(.branch 189565
(.leaf ⟨189545,20,(.group 3 456 false)⟩)
(.leaf ⟨189565,20,(.group 3 457 false)⟩))))
(.branch 189665
(.branch 189625
(.branch 189605
(.leaf ⟨189585,20,(.group 3 458 false)⟩)
(.leaf ⟨189605,20,(.group 3 459 false)⟩))
(.branch 189645
(.leaf ⟨189625,20,(.group 3 460 false)⟩)
(.leaf ⟨189645,20,(.group 3 461 false)⟩)))
(.branch 189705
(.branch 189685
(.leaf ⟨189665,20,(.group 3 462 false)⟩)
(.leaf ⟨189685,20,(.group 3 463 false)⟩))
(.branch 189725
(.leaf ⟨189705,20,(.group 3 464 false)⟩)
(.leaf ⟨189725,20,(.group 3 465 false)⟩))))))
(.branch 190065
(.branch 189905
(.branch 189825
(.branch 189785
(.branch 189765
(.leaf ⟨189745,20,(.group 3 466 false)⟩)
(.leaf ⟨189765,20,(.group 3 467 false)⟩))
(.branch 189805
(.leaf ⟨189785,20,(.group 3 468 false)⟩)
(.leaf ⟨189805,20,(.group 3 469 false)⟩)))
(.branch 189865
(.branch 189845
(.leaf ⟨189825,20,(.group 3 470 false)⟩)
(.leaf ⟨189845,20,(.group 3 471 false)⟩))
(.branch 189885
(.leaf ⟨189865,20,(.group 3 472 false)⟩)
(.leaf ⟨189885,20,(.group 3 473 false)⟩))))
(.branch 189985
(.branch 189945
(.branch 189925
(.leaf ⟨189905,20,(.group 3 474 false)⟩)
(.leaf ⟨189925,20,(.group 3 475 false)⟩))
(.branch 189965
(.leaf ⟨189945,20,(.group 3 476 false)⟩)
(.leaf ⟨189965,20,(.group 3 477 false)⟩)))
(.branch 190025
(.branch 190005
(.leaf ⟨189985,20,(.group 3 478 false)⟩)
(.leaf ⟨190005,20,(.group 3 479 false)⟩))
(.branch 190045
(.leaf ⟨190025,20,(.group 3 480 false)⟩)
(.leaf ⟨190045,20,(.group 3 481 false)⟩)))))
(.branch 190225
(.branch 190145
(.branch 190105
(.branch 190085
(.leaf ⟨190065,20,(.group 3 482 false)⟩)
(.leaf ⟨190085,20,(.group 3 483 false)⟩))
(.branch 190125
(.leaf ⟨190105,20,(.group 3 484 false)⟩)
(.leaf ⟨190125,20,(.group 3 485 false)⟩)))
(.branch 190185
(.branch 190165
(.leaf ⟨190145,20,(.group 3 486 false)⟩)
(.leaf ⟨190165,20,(.group 3 487 false)⟩))
(.branch 190205
(.leaf ⟨190185,20,(.group 3 488 false)⟩)
(.leaf ⟨190205,20,(.group 3 489 false)⟩))))
(.branch 190305
(.branch 190265
(.branch 190245
(.leaf ⟨190225,20,(.group 3 490 false)⟩)
(.leaf ⟨190245,20,(.group 3 491 false)⟩))
(.branch 190285
(.leaf ⟨190265,20,(.group 3 492 false)⟩)
(.leaf ⟨190285,20,(.group 3 493 false)⟩)))
(.branch 190345
(.branch 190325
(.leaf ⟨190305,20,(.group 3 494 false)⟩)
(.leaf ⟨190325,20,(.group 3 495 false)⟩))
(.branch 190365
(.leaf ⟨190345,20,(.group 3 496 false)⟩)
(.leaf ⟨190365,20,(.group 3 497 false)⟩)))))))

theorem tree181_checked : tree181.check 189105 190385 = true := by decide +kernel

def tree182 : Tree := (.branch 191025
(.branch 190705
(.branch 190545
(.branch 190465
(.branch 190425
(.branch 190405
(.leaf ⟨190385,20,(.group 3 498 false)⟩)
(.leaf ⟨190405,20,(.group 3 499 false)⟩))
(.branch 190445
(.leaf ⟨190425,20,(.group 3 500 false)⟩)
(.leaf ⟨190445,20,(.group 3 501 false)⟩)))
(.branch 190505
(.branch 190485
(.leaf ⟨190465,20,(.group 3 502 false)⟩)
(.leaf ⟨190485,20,(.group 3 503 false)⟩))
(.branch 190525
(.leaf ⟨190505,20,(.group 3 504 false)⟩)
(.leaf ⟨190525,20,(.group 3 505 false)⟩))))
(.branch 190625
(.branch 190585
(.branch 190565
(.leaf ⟨190545,20,(.group 3 506 false)⟩)
(.leaf ⟨190565,20,(.group 3 507 false)⟩))
(.branch 190605
(.leaf ⟨190585,20,(.group 3 508 false)⟩)
(.leaf ⟨190605,20,(.group 3 509 false)⟩)))
(.branch 190665
(.branch 190645
(.leaf ⟨190625,20,(.group 3 510 false)⟩)
(.leaf ⟨190645,20,(.group 3 511 false)⟩))
(.branch 190685
(.leaf ⟨190665,20,(.group 4 455 false)⟩)
(.leaf ⟨190685,20,(.group 4 456 false)⟩)))))
(.branch 190865
(.branch 190785
(.branch 190745
(.branch 190725
(.leaf ⟨190705,20,(.group 4 457 false)⟩)
(.leaf ⟨190725,20,(.group 4 458 false)⟩))
(.branch 190765
(.leaf ⟨190745,20,(.group 4 459 false)⟩)
(.leaf ⟨190765,20,(.group 4 460 false)⟩)))
(.branch 190825
(.branch 190805
(.leaf ⟨190785,20,(.group 4 461 false)⟩)
(.leaf ⟨190805,20,(.group 4 462 false)⟩))
(.branch 190845
(.leaf ⟨190825,20,(.group 4 463 false)⟩)
(.leaf ⟨190845,20,(.group 4 464 false)⟩))))
(.branch 190945
(.branch 190905
(.branch 190885
(.leaf ⟨190865,20,(.group 4 465 false)⟩)
(.leaf ⟨190885,20,(.group 4 466 false)⟩))
(.branch 190925
(.leaf ⟨190905,20,(.group 4 467 false)⟩)
(.leaf ⟨190925,20,(.group 4 468 false)⟩)))
(.branch 190985
(.branch 190965
(.leaf ⟨190945,20,(.group 4 469 false)⟩)
(.leaf ⟨190965,20,(.group 4 470 false)⟩))
(.branch 191005
(.leaf ⟨190985,20,(.group 4 471 false)⟩)
(.leaf ⟨191005,20,(.group 4 472 false)⟩))))))
(.branch 191345
(.branch 191185
(.branch 191105
(.branch 191065
(.branch 191045
(.leaf ⟨191025,20,(.group 4 473 false)⟩)
(.leaf ⟨191045,20,(.group 4 474 false)⟩))
(.branch 191085
(.leaf ⟨191065,20,(.group 4 475 false)⟩)
(.leaf ⟨191085,20,(.group 4 476 false)⟩)))
(.branch 191145
(.branch 191125
(.leaf ⟨191105,20,(.group 4 477 false)⟩)
(.leaf ⟨191125,20,(.group 4 478 false)⟩))
(.branch 191165
(.leaf ⟨191145,20,(.group 4 479 false)⟩)
(.leaf ⟨191165,20,(.group 4 480 false)⟩))))
(.branch 191265
(.branch 191225
(.branch 191205
(.leaf ⟨191185,20,(.group 4 481 false)⟩)
(.leaf ⟨191205,20,(.group 4 482 false)⟩))
(.branch 191245
(.leaf ⟨191225,20,(.group 4 483 false)⟩)
(.leaf ⟨191245,20,(.group 4 484 false)⟩)))
(.branch 191305
(.branch 191285
(.leaf ⟨191265,20,(.group 4 485 false)⟩)
(.leaf ⟨191285,20,(.group 4 486 false)⟩))
(.branch 191325
(.leaf ⟨191305,20,(.group 4 487 false)⟩)
(.leaf ⟨191325,20,(.group 4 488 false)⟩)))))
(.branch 191505
(.branch 191425
(.branch 191385
(.branch 191365
(.leaf ⟨191345,20,(.group 4 489 false)⟩)
(.leaf ⟨191365,20,(.group 4 490 false)⟩))
(.branch 191405
(.leaf ⟨191385,20,(.group 4 491 false)⟩)
(.leaf ⟨191405,20,(.group 4 492 false)⟩)))
(.branch 191465
(.branch 191445
(.leaf ⟨191425,20,(.group 4 493 false)⟩)
(.leaf ⟨191445,20,(.group 4 494 false)⟩))
(.branch 191485
(.leaf ⟨191465,20,(.group 4 495 false)⟩)
(.leaf ⟨191485,20,(.group 4 496 false)⟩))))
(.branch 191585
(.branch 191545
(.branch 191525
(.leaf ⟨191505,20,(.group 4 497 false)⟩)
(.leaf ⟨191525,20,(.group 4 498 false)⟩))
(.branch 191565
(.leaf ⟨191545,20,(.group 4 499 false)⟩)
(.leaf ⟨191565,20,(.group 4 500 false)⟩)))
(.branch 191625
(.branch 191605
(.leaf ⟨191585,20,(.group 4 501 false)⟩)
(.leaf ⟨191605,20,(.group 4 502 false)⟩))
(.branch 191645
(.leaf ⟨191625,20,(.group 4 503 false)⟩)
(.leaf ⟨191645,20,(.group 4 504 false)⟩)))))))

theorem tree182_checked : tree182.check 190385 191665 = true := by decide +kernel

def tree183 : Tree := (.branch 192305
(.branch 191985
(.branch 191825
(.branch 191745
(.branch 191705
(.branch 191685
(.leaf ⟨191665,20,(.group 4 505 false)⟩)
(.leaf ⟨191685,20,(.group 4 506 false)⟩))
(.branch 191725
(.leaf ⟨191705,20,(.group 4 507 false)⟩)
(.leaf ⟨191725,20,(.group 4 508 false)⟩)))
(.branch 191785
(.branch 191765
(.leaf ⟨191745,20,(.group 4 509 false)⟩)
(.leaf ⟨191765,20,(.group 4 510 false)⟩))
(.branch 191805
(.leaf ⟨191785,20,(.group 4 511 false)⟩)
(.leaf ⟨191805,20,(.group 5 2894 false)⟩))))
(.branch 191905
(.branch 191865
(.branch 191845
(.leaf ⟨191825,20,(.group 5 2895 false)⟩)
(.leaf ⟨191845,20,(.group 5 2896 false)⟩))
(.branch 191885
(.leaf ⟨191865,20,(.group 5 2897 false)⟩)
(.leaf ⟨191885,20,(.group 5 2898 false)⟩)))
(.branch 191945
(.branch 191925
(.leaf ⟨191905,20,(.group 5 2899 false)⟩)
(.leaf ⟨191925,20,(.group 5 2900 false)⟩))
(.branch 191965
(.leaf ⟨191945,20,(.group 5 2901 false)⟩)
(.leaf ⟨191965,20,(.group 5 2902 false)⟩)))))
(.branch 192145
(.branch 192065
(.branch 192025
(.branch 192005
(.leaf ⟨191985,20,(.group 5 2903 false)⟩)
(.leaf ⟨192005,20,(.group 5 2904 false)⟩))
(.branch 192045
(.leaf ⟨192025,20,(.group 5 2905 false)⟩)
(.leaf ⟨192045,20,(.group 5 2906 false)⟩)))
(.branch 192105
(.branch 192085
(.leaf ⟨192065,20,(.group 5 2907 false)⟩)
(.leaf ⟨192085,20,(.group 5 2908 false)⟩))
(.branch 192125
(.leaf ⟨192105,20,(.group 5 2909 false)⟩)
(.leaf ⟨192125,20,(.group 5 2910 false)⟩))))
(.branch 192225
(.branch 192185
(.branch 192165
(.leaf ⟨192145,20,(.group 5 2911 false)⟩)
(.leaf ⟨192165,20,(.group 5 2912 false)⟩))
(.branch 192205
(.leaf ⟨192185,20,(.group 5 2913 false)⟩)
(.leaf ⟨192205,20,(.group 5 2914 false)⟩)))
(.branch 192265
(.branch 192245
(.leaf ⟨192225,20,(.group 5 2915 false)⟩)
(.leaf ⟨192245,20,(.group 5 2916 false)⟩))
(.branch 192285
(.leaf ⟨192265,20,(.group 5 2917 false)⟩)
(.leaf ⟨192285,20,(.group 5 2918 false)⟩))))))
(.branch 192625
(.branch 192465
(.branch 192385
(.branch 192345
(.branch 192325
(.leaf ⟨192305,20,(.group 5 2919 false)⟩)
(.leaf ⟨192325,20,(.group 5 2920 false)⟩))
(.branch 192365
(.leaf ⟨192345,20,(.group 5 2921 false)⟩)
(.leaf ⟨192365,20,(.group 5 2922 false)⟩)))
(.branch 192425
(.branch 192405
(.leaf ⟨192385,20,(.group 5 2923 false)⟩)
(.leaf ⟨192405,20,(.group 5 2924 false)⟩))
(.branch 192445
(.leaf ⟨192425,20,(.group 5 2925 false)⟩)
(.leaf ⟨192445,20,(.group 5 2926 false)⟩))))
(.branch 192545
(.branch 192505
(.branch 192485
(.leaf ⟨192465,20,(.group 5 2927 false)⟩)
(.leaf ⟨192485,20,(.group 5 2928 false)⟩))
(.branch 192525
(.leaf ⟨192505,20,(.group 5 2929 false)⟩)
(.leaf ⟨192525,20,(.group 5 2930 false)⟩)))
(.branch 192585
(.branch 192565
(.leaf ⟨192545,20,(.group 5 2931 false)⟩)
(.leaf ⟨192565,20,(.group 5 2932 false)⟩))
(.branch 192605
(.leaf ⟨192585,20,(.group 5 2933 false)⟩)
(.leaf ⟨192605,20,(.group 5 2934 false)⟩)))))
(.branch 192785
(.branch 192705
(.branch 192665
(.branch 192645
(.leaf ⟨192625,20,(.group 5 2935 false)⟩)
(.leaf ⟨192645,20,(.group 5 2936 false)⟩))
(.branch 192685
(.leaf ⟨192665,20,(.group 5 2937 false)⟩)
(.leaf ⟨192685,20,(.group 5 2938 false)⟩)))
(.branch 192745
(.branch 192725
(.leaf ⟨192705,20,(.group 5 2939 false)⟩)
(.leaf ⟨192725,20,(.group 5 2940 false)⟩))
(.branch 192765
(.leaf ⟨192745,20,(.group 5 2941 false)⟩)
(.leaf ⟨192765,20,(.group 5 2942 false)⟩))))
(.branch 192865
(.branch 192825
(.branch 192805
(.leaf ⟨192785,20,(.group 5 2943 false)⟩)
(.leaf ⟨192805,20,(.group 5 2944 false)⟩))
(.branch 192845
(.leaf ⟨192825,20,(.group 5 2945 false)⟩)
(.leaf ⟨192845,20,(.group 5 2946 false)⟩)))
(.branch 192905
(.branch 192885
(.leaf ⟨192865,20,(.group 5 2947 false)⟩)
(.leaf ⟨192885,20,(.group 5 2948 false)⟩))
(.branch 192925
(.leaf ⟨192905,20,(.group 5 2949 false)⟩)
(.leaf ⟨192925,20,(.group 5 2950 false)⟩)))))))

theorem tree183_checked : tree183.check 191665 192945 = true := by decide +kernel

def tree184 : Tree := (.branch 193585
(.branch 193265
(.branch 193105
(.branch 193025
(.branch 192985
(.branch 192965
(.leaf ⟨192945,20,(.group 5 2951 false)⟩)
(.leaf ⟨192965,20,(.group 5 2952 false)⟩))
(.branch 193005
(.leaf ⟨192985,20,(.group 5 2953 false)⟩)
(.leaf ⟨193005,20,(.group 5 2954 false)⟩)))
(.branch 193065
(.branch 193045
(.leaf ⟨193025,20,(.group 5 2955 false)⟩)
(.leaf ⟨193045,20,(.group 5 2956 false)⟩))
(.branch 193085
(.leaf ⟨193065,20,(.group 5 2957 false)⟩)
(.leaf ⟨193085,20,(.group 5 2958 false)⟩))))
(.branch 193185
(.branch 193145
(.branch 193125
(.leaf ⟨193105,20,(.group 5 2959 false)⟩)
(.leaf ⟨193125,20,(.group 5 2960 false)⟩))
(.branch 193165
(.leaf ⟨193145,20,(.group 5 2961 false)⟩)
(.leaf ⟨193165,20,(.group 5 2962 false)⟩)))
(.branch 193225
(.branch 193205
(.leaf ⟨193185,20,(.group 5 2963 false)⟩)
(.leaf ⟨193205,20,(.group 5 2964 false)⟩))
(.branch 193245
(.leaf ⟨193225,20,(.group 5 2965 false)⟩)
(.leaf ⟨193245,20,(.group 5 2966 false)⟩)))))
(.branch 193425
(.branch 193345
(.branch 193305
(.branch 193285
(.leaf ⟨193265,20,(.group 5 2967 false)⟩)
(.leaf ⟨193285,20,(.group 5 2968 false)⟩))
(.branch 193325
(.leaf ⟨193305,20,(.group 5 2969 false)⟩)
(.leaf ⟨193325,20,(.group 5 2970 false)⟩)))
(.branch 193385
(.branch 193365
(.leaf ⟨193345,20,(.group 5 2971 false)⟩)
(.leaf ⟨193365,20,(.group 5 2972 false)⟩))
(.branch 193405
(.leaf ⟨193385,20,(.group 5 2973 false)⟩)
(.leaf ⟨193405,20,(.group 5 2974 false)⟩))))
(.branch 193505
(.branch 193465
(.branch 193445
(.leaf ⟨193425,20,(.group 5 2975 false)⟩)
(.leaf ⟨193445,20,(.group 5 2976 false)⟩))
(.branch 193485
(.leaf ⟨193465,20,(.group 5 2977 false)⟩)
(.leaf ⟨193485,20,(.group 5 2978 false)⟩)))
(.branch 193545
(.branch 193525
(.leaf ⟨193505,20,(.group 5 2979 false)⟩)
(.leaf ⟨193525,20,(.group 5 2980 false)⟩))
(.branch 193565
(.leaf ⟨193545,20,(.group 5 2981 false)⟩)
(.leaf ⟨193565,20,(.group 5 2982 false)⟩))))))
(.branch 193905
(.branch 193745
(.branch 193665
(.branch 193625
(.branch 193605
(.leaf ⟨193585,20,(.group 5 2983 false)⟩)
(.leaf ⟨193605,20,(.group 5 2984 false)⟩))
(.branch 193645
(.leaf ⟨193625,20,(.group 5 2985 false)⟩)
(.leaf ⟨193645,20,(.group 5 2986 false)⟩)))
(.branch 193705
(.branch 193685
(.leaf ⟨193665,20,(.group 5 2987 false)⟩)
(.leaf ⟨193685,20,(.group 5 2988 false)⟩))
(.branch 193725
(.leaf ⟨193705,20,(.group 5 2989 false)⟩)
(.leaf ⟨193725,20,(.group 5 2990 false)⟩))))
(.branch 193825
(.branch 193785
(.branch 193765
(.leaf ⟨193745,20,(.group 5 2991 false)⟩)
(.leaf ⟨193765,20,(.group 5 2992 false)⟩))
(.branch 193805
(.leaf ⟨193785,20,(.group 5 2993 false)⟩)
(.leaf ⟨193805,20,(.group 5 2994 false)⟩)))
(.branch 193865
(.branch 193845
(.leaf ⟨193825,20,(.group 5 2995 false)⟩)
(.leaf ⟨193845,20,(.group 5 2996 false)⟩))
(.branch 193885
(.leaf ⟨193865,20,(.group 5 2997 false)⟩)
(.leaf ⟨193885,20,(.group 5 2998 false)⟩)))))
(.branch 194065
(.branch 193985
(.branch 193945
(.branch 193925
(.leaf ⟨193905,20,(.group 5 2999 false)⟩)
(.leaf ⟨193925,20,(.group 5 3000 false)⟩))
(.branch 193965
(.leaf ⟨193945,20,(.group 5 3001 false)⟩)
(.leaf ⟨193965,20,(.group 5 3002 false)⟩)))
(.branch 194025
(.branch 194005
(.leaf ⟨193985,20,(.group 5 3003 false)⟩)
(.leaf ⟨194005,20,(.group 5 3004 false)⟩))
(.branch 194045
(.leaf ⟨194025,20,(.group 5 3005 false)⟩)
(.leaf ⟨194045,20,(.group 5 3006 false)⟩))))
(.branch 194145
(.branch 194105
(.branch 194085
(.leaf ⟨194065,20,(.group 5 3007 false)⟩)
(.leaf ⟨194085,20,(.group 5 3008 false)⟩))
(.branch 194125
(.leaf ⟨194105,20,(.group 5 3009 false)⟩)
(.leaf ⟨194125,20,(.group 5 3010 false)⟩)))
(.branch 194185
(.branch 194165
(.leaf ⟨194145,20,(.group 5 3011 false)⟩)
(.leaf ⟨194165,20,(.group 5 3012 false)⟩))
(.branch 194205
(.leaf ⟨194185,20,(.group 5 3013 false)⟩)
(.leaf ⟨194205,20,(.group 5 3014 false)⟩)))))))

theorem tree184_checked : tree184.check 192945 194225 = true := by decide +kernel

def tree185 : Tree := (.branch 194865
(.branch 194545
(.branch 194385
(.branch 194305
(.branch 194265
(.branch 194245
(.leaf ⟨194225,20,(.group 5 3015 false)⟩)
(.leaf ⟨194245,20,(.group 5 3016 false)⟩))
(.branch 194285
(.leaf ⟨194265,20,(.group 5 3017 false)⟩)
(.leaf ⟨194285,20,(.group 5 3018 false)⟩)))
(.branch 194345
(.branch 194325
(.leaf ⟨194305,20,(.group 5 3019 false)⟩)
(.leaf ⟨194325,20,(.group 5 3020 false)⟩))
(.branch 194365
(.leaf ⟨194345,20,(.group 5 3021 false)⟩)
(.leaf ⟨194365,20,(.group 5 3022 false)⟩))))
(.branch 194465
(.branch 194425
(.branch 194405
(.leaf ⟨194385,20,(.group 5 3023 false)⟩)
(.leaf ⟨194405,20,(.group 5 3024 false)⟩))
(.branch 194445
(.leaf ⟨194425,20,(.group 5 3025 false)⟩)
(.leaf ⟨194445,20,(.group 5 3026 false)⟩)))
(.branch 194505
(.branch 194485
(.leaf ⟨194465,20,(.group 5 3027 false)⟩)
(.leaf ⟨194485,20,(.group 5 3028 false)⟩))
(.branch 194525
(.leaf ⟨194505,20,(.group 5 3029 false)⟩)
(.leaf ⟨194525,20,(.group 5 3030 false)⟩)))))
(.branch 194705
(.branch 194625
(.branch 194585
(.branch 194565
(.leaf ⟨194545,20,(.group 5 3031 false)⟩)
(.leaf ⟨194565,20,(.group 5 3032 false)⟩))
(.branch 194605
(.leaf ⟨194585,20,(.group 5 3033 false)⟩)
(.leaf ⟨194605,20,(.group 5 3034 false)⟩)))
(.branch 194665
(.branch 194645
(.leaf ⟨194625,20,(.group 5 3035 false)⟩)
(.leaf ⟨194645,20,(.group 5 3036 false)⟩))
(.branch 194685
(.leaf ⟨194665,20,(.group 5 3037 false)⟩)
(.leaf ⟨194685,20,(.group 5 3038 false)⟩))))
(.branch 194785
(.branch 194745
(.branch 194725
(.leaf ⟨194705,20,(.group 5 3039 false)⟩)
(.leaf ⟨194725,20,(.group 5 3040 false)⟩))
(.branch 194765
(.leaf ⟨194745,20,(.group 5 3041 false)⟩)
(.leaf ⟨194765,20,(.group 5 3042 false)⟩)))
(.branch 194825
(.branch 194805
(.leaf ⟨194785,20,(.group 5 3043 false)⟩)
(.leaf ⟨194805,20,(.group 5 3044 false)⟩))
(.branch 194845
(.leaf ⟨194825,20,(.group 5 3045 false)⟩)
(.leaf ⟨194845,20,(.group 5 3046 false)⟩))))))
(.branch 195185
(.branch 195025
(.branch 194945
(.branch 194905
(.branch 194885
(.leaf ⟨194865,20,(.group 5 3047 false)⟩)
(.leaf ⟨194885,20,(.group 5 3048 false)⟩))
(.branch 194925
(.leaf ⟨194905,20,(.group 5 3049 false)⟩)
(.leaf ⟨194925,20,(.group 5 3050 false)⟩)))
(.branch 194985
(.branch 194965
(.leaf ⟨194945,20,(.group 5 3051 false)⟩)
(.leaf ⟨194965,20,(.group 5 3052 false)⟩))
(.branch 195005
(.leaf ⟨194985,20,(.group 5 3053 false)⟩)
(.leaf ⟨195005,20,(.group 5 3054 false)⟩))))
(.branch 195105
(.branch 195065
(.branch 195045
(.leaf ⟨195025,20,(.group 5 3055 false)⟩)
(.leaf ⟨195045,20,(.group 5 3056 false)⟩))
(.branch 195085
(.leaf ⟨195065,20,(.group 5 3057 false)⟩)
(.leaf ⟨195085,20,(.group 5 3058 false)⟩)))
(.branch 195145
(.branch 195125
(.leaf ⟨195105,20,(.group 5 3059 false)⟩)
(.leaf ⟨195125,20,(.group 5 3060 false)⟩))
(.branch 195165
(.leaf ⟨195145,20,(.group 5 3061 false)⟩)
(.leaf ⟨195165,20,(.group 5 3062 false)⟩)))))
(.branch 195345
(.branch 195265
(.branch 195225
(.branch 195205
(.leaf ⟨195185,20,(.group 5 3063 false)⟩)
(.leaf ⟨195205,20,(.group 5 3064 false)⟩))
(.branch 195245
(.leaf ⟨195225,20,(.group 5 3065 false)⟩)
(.leaf ⟨195245,20,(.group 5 3066 false)⟩)))
(.branch 195305
(.branch 195285
(.leaf ⟨195265,20,(.group 5 3067 false)⟩)
(.leaf ⟨195285,20,(.group 5 3068 false)⟩))
(.branch 195325
(.leaf ⟨195305,20,(.group 5 3069 false)⟩)
(.leaf ⟨195325,20,(.group 5 3070 false)⟩))))
(.branch 195425
(.branch 195385
(.branch 195365
(.leaf ⟨195345,20,(.group 5 3071 false)⟩)
(.leaf ⟨195365,20,(.group 5 3072 false)⟩))
(.branch 195405
(.leaf ⟨195385,20,(.group 5 3073 false)⟩)
(.leaf ⟨195405,20,(.group 5 3074 false)⟩)))
(.branch 195465
(.branch 195445
(.leaf ⟨195425,20,(.group 5 3075 false)⟩)
(.leaf ⟨195445,20,(.group 5 3076 false)⟩))
(.branch 195485
(.leaf ⟨195465,20,(.group 5 3077 false)⟩)
(.leaf ⟨195485,20,(.group 5 3078 false)⟩)))))))

theorem tree185_checked : tree185.check 194225 195505 = true := by decide +kernel

def tree186 : Tree := (.branch 196145
(.branch 195825
(.branch 195665
(.branch 195585
(.branch 195545
(.branch 195525
(.leaf ⟨195505,20,(.group 5 3079 false)⟩)
(.leaf ⟨195525,20,(.group 5 3080 false)⟩))
(.branch 195565
(.leaf ⟨195545,20,(.group 5 3081 false)⟩)
(.leaf ⟨195565,20,(.group 5 3082 false)⟩)))
(.branch 195625
(.branch 195605
(.leaf ⟨195585,20,(.group 5 3083 false)⟩)
(.leaf ⟨195605,20,(.group 5 3084 false)⟩))
(.branch 195645
(.leaf ⟨195625,20,(.group 5 3085 false)⟩)
(.leaf ⟨195645,20,(.group 5 3086 false)⟩))))
(.branch 195745
(.branch 195705
(.branch 195685
(.leaf ⟨195665,20,(.group 5 3087 false)⟩)
(.leaf ⟨195685,20,(.group 5 3088 false)⟩))
(.branch 195725
(.leaf ⟨195705,20,(.group 5 3089 false)⟩)
(.leaf ⟨195725,20,(.group 5 3090 false)⟩)))
(.branch 195785
(.branch 195765
(.leaf ⟨195745,20,(.group 5 3091 false)⟩)
(.leaf ⟨195765,20,(.group 5 3092 false)⟩))
(.branch 195805
(.leaf ⟨195785,20,(.group 5 3093 false)⟩)
(.leaf ⟨195805,20,(.group 5 3094 false)⟩)))))
(.branch 195985
(.branch 195905
(.branch 195865
(.branch 195845
(.leaf ⟨195825,20,(.group 5 3095 false)⟩)
(.leaf ⟨195845,20,(.group 5 3096 false)⟩))
(.branch 195885
(.leaf ⟨195865,20,(.group 5 3097 false)⟩)
(.leaf ⟨195885,20,(.group 5 3098 false)⟩)))
(.branch 195945
(.branch 195925
(.leaf ⟨195905,20,(.group 5 3099 false)⟩)
(.leaf ⟨195925,20,(.group 5 3100 false)⟩))
(.branch 195965
(.leaf ⟨195945,20,(.group 5 3101 false)⟩)
(.leaf ⟨195965,20,(.group 5 3102 false)⟩))))
(.branch 196065
(.branch 196025
(.branch 196005
(.leaf ⟨195985,20,(.group 5 3103 false)⟩)
(.leaf ⟨196005,20,(.group 5 3104 false)⟩))
(.branch 196045
(.leaf ⟨196025,20,(.group 5 3105 false)⟩)
(.leaf ⟨196045,20,(.group 5 3106 false)⟩)))
(.branch 196105
(.branch 196085
(.leaf ⟨196065,20,(.group 5 3107 false)⟩)
(.leaf ⟨196085,20,(.group 5 3108 false)⟩))
(.branch 196125
(.leaf ⟨196105,20,(.group 5 3109 false)⟩)
(.leaf ⟨196125,20,(.group 5 3110 false)⟩))))))
(.branch 196465
(.branch 196305
(.branch 196225
(.branch 196185
(.branch 196165
(.leaf ⟨196145,20,(.group 5 3111 false)⟩)
(.leaf ⟨196165,20,(.group 5 3112 false)⟩))
(.branch 196205
(.leaf ⟨196185,20,(.group 5 3113 false)⟩)
(.leaf ⟨196205,20,(.group 5 3114 false)⟩)))
(.branch 196265
(.branch 196245
(.leaf ⟨196225,20,(.group 5 3115 false)⟩)
(.leaf ⟨196245,20,(.group 5 3116 false)⟩))
(.branch 196285
(.leaf ⟨196265,20,(.group 5 3117 false)⟩)
(.leaf ⟨196285,20,(.group 5 3118 false)⟩))))
(.branch 196385
(.branch 196345
(.branch 196325
(.leaf ⟨196305,20,(.group 5 3119 false)⟩)
(.leaf ⟨196325,20,(.group 5 3120 false)⟩))
(.branch 196365
(.leaf ⟨196345,20,(.group 5 3121 false)⟩)
(.leaf ⟨196365,20,(.group 5 3122 false)⟩)))
(.branch 196425
(.branch 196405
(.leaf ⟨196385,20,(.group 5 3123 false)⟩)
(.leaf ⟨196405,20,(.group 5 3124 false)⟩))
(.branch 196445
(.leaf ⟨196425,20,(.group 5 3125 false)⟩)
(.leaf ⟨196445,20,(.group 5 3126 false)⟩)))))
(.branch 196625
(.branch 196545
(.branch 196505
(.branch 196485
(.leaf ⟨196465,20,(.group 5 3127 false)⟩)
(.leaf ⟨196485,20,(.group 5 3128 false)⟩))
(.branch 196525
(.leaf ⟨196505,20,(.group 5 3129 false)⟩)
(.leaf ⟨196525,20,(.group 5 3130 false)⟩)))
(.branch 196585
(.branch 196565
(.leaf ⟨196545,20,(.group 5 3131 false)⟩)
(.leaf ⟨196565,20,(.group 5 3132 false)⟩))
(.branch 196605
(.leaf ⟨196585,20,(.group 5 3133 false)⟩)
(.leaf ⟨196605,20,(.group 5 3134 false)⟩))))
(.branch 196705
(.branch 196665
(.branch 196645
(.leaf ⟨196625,20,(.group 5 3135 false)⟩)
(.leaf ⟨196645,20,(.group 5 3136 false)⟩))
(.branch 196685
(.leaf ⟨196665,20,(.group 5 3137 false)⟩)
(.leaf ⟨196685,20,(.group 5 3138 false)⟩)))
(.branch 196745
(.branch 196725
(.leaf ⟨196705,20,(.group 5 3139 false)⟩)
(.leaf ⟨196725,20,(.group 5 3140 false)⟩))
(.branch 196765
(.leaf ⟨196745,20,(.group 5 3141 false)⟩)
(.leaf ⟨196765,20,(.group 5 3142 false)⟩)))))))

theorem tree186_checked : tree186.check 195505 196785 = true := by decide +kernel

def tree187 : Tree := (.branch 197425
(.branch 197105
(.branch 196945
(.branch 196865
(.branch 196825
(.branch 196805
(.leaf ⟨196785,20,(.group 5 3143 false)⟩)
(.leaf ⟨196805,20,(.group 5 3144 false)⟩))
(.branch 196845
(.leaf ⟨196825,20,(.group 5 3145 false)⟩)
(.leaf ⟨196845,20,(.group 5 3146 false)⟩)))
(.branch 196905
(.branch 196885
(.leaf ⟨196865,20,(.group 5 3147 false)⟩)
(.leaf ⟨196885,20,(.group 5 3148 false)⟩))
(.branch 196925
(.leaf ⟨196905,20,(.group 5 3149 false)⟩)
(.leaf ⟨196925,20,(.group 5 3150 false)⟩))))
(.branch 197025
(.branch 196985
(.branch 196965
(.leaf ⟨196945,20,(.group 5 3151 false)⟩)
(.leaf ⟨196965,20,(.group 5 3152 false)⟩))
(.branch 197005
(.leaf ⟨196985,20,(.group 5 3153 false)⟩)
(.leaf ⟨197005,20,(.group 5 3154 false)⟩)))
(.branch 197065
(.branch 197045
(.leaf ⟨197025,20,(.group 5 3155 false)⟩)
(.leaf ⟨197045,20,(.group 5 3156 false)⟩))
(.branch 197085
(.leaf ⟨197065,20,(.group 5 3157 false)⟩)
(.leaf ⟨197085,20,(.group 5 3158 false)⟩)))))
(.branch 197265
(.branch 197185
(.branch 197145
(.branch 197125
(.leaf ⟨197105,20,(.group 5 3159 false)⟩)
(.leaf ⟨197125,20,(.group 5 3160 false)⟩))
(.branch 197165
(.leaf ⟨197145,20,(.group 5 3161 false)⟩)
(.leaf ⟨197165,20,(.group 5 3162 false)⟩)))
(.branch 197225
(.branch 197205
(.leaf ⟨197185,20,(.group 5 3163 false)⟩)
(.leaf ⟨197205,20,(.group 5 3164 false)⟩))
(.branch 197245
(.leaf ⟨197225,20,(.group 5 3165 false)⟩)
(.leaf ⟨197245,20,(.group 5 3166 false)⟩))))
(.branch 197345
(.branch 197305
(.branch 197285
(.leaf ⟨197265,20,(.group 5 3167 false)⟩)
(.leaf ⟨197285,20,(.group 5 3168 false)⟩))
(.branch 197325
(.leaf ⟨197305,20,(.group 5 3169 false)⟩)
(.leaf ⟨197325,20,(.group 5 3170 false)⟩)))
(.branch 197385
(.branch 197365
(.leaf ⟨197345,20,(.group 5 3171 false)⟩)
(.leaf ⟨197365,20,(.group 5 3172 false)⟩))
(.branch 197405
(.leaf ⟨197385,20,(.group 5 3173 false)⟩)
(.leaf ⟨197405,20,(.group 5 3174 false)⟩))))))
(.branch 197745
(.branch 197585
(.branch 197505
(.branch 197465
(.branch 197445
(.leaf ⟨197425,20,(.group 5 3175 false)⟩)
(.leaf ⟨197445,20,(.group 5 3176 false)⟩))
(.branch 197485
(.leaf ⟨197465,20,(.group 5 3177 false)⟩)
(.leaf ⟨197485,20,(.group 5 3178 false)⟩)))
(.branch 197545
(.branch 197525
(.leaf ⟨197505,20,(.group 5 3179 false)⟩)
(.leaf ⟨197525,20,(.group 5 3180 false)⟩))
(.branch 197565
(.leaf ⟨197545,20,(.group 5 3181 false)⟩)
(.leaf ⟨197565,20,(.group 5 3182 false)⟩))))
(.branch 197665
(.branch 197625
(.branch 197605
(.leaf ⟨197585,20,(.group 5 3183 false)⟩)
(.leaf ⟨197605,20,(.group 5 3184 false)⟩))
(.branch 197645
(.leaf ⟨197625,20,(.group 5 3185 false)⟩)
(.leaf ⟨197645,20,(.group 5 3186 false)⟩)))
(.branch 197705
(.branch 197685
(.leaf ⟨197665,20,(.group 5 3187 false)⟩)
(.leaf ⟨197685,20,(.group 5 3188 false)⟩))
(.branch 197725
(.leaf ⟨197705,20,(.group 5 3189 false)⟩)
(.leaf ⟨197725,20,(.group 5 3190 false)⟩)))))
(.branch 197905
(.branch 197825
(.branch 197785
(.branch 197765
(.leaf ⟨197745,20,(.group 5 3191 false)⟩)
(.leaf ⟨197765,20,(.group 5 3192 false)⟩))
(.branch 197805
(.leaf ⟨197785,20,(.group 5 3193 false)⟩)
(.leaf ⟨197805,20,(.group 5 3194 false)⟩)))
(.branch 197865
(.branch 197845
(.leaf ⟨197825,20,(.group 5 3195 false)⟩)
(.leaf ⟨197845,20,(.group 5 3196 false)⟩))
(.branch 197885
(.leaf ⟨197865,20,(.group 5 3197 false)⟩)
(.leaf ⟨197885,20,(.group 5 3198 false)⟩))))
(.branch 197985
(.branch 197945
(.branch 197925
(.leaf ⟨197905,20,(.group 5 3199 false)⟩)
(.leaf ⟨197925,20,(.group 5 3200 false)⟩))
(.branch 197965
(.leaf ⟨197945,20,(.group 5 3201 false)⟩)
(.leaf ⟨197965,20,(.group 5 3202 false)⟩)))
(.branch 198025
(.branch 198005
(.leaf ⟨197985,20,(.group 5 3203 false)⟩)
(.leaf ⟨198005,20,(.group 5 3204 false)⟩))
(.branch 198045
(.leaf ⟨198025,20,(.group 5 3205 false)⟩)
(.leaf ⟨198045,20,(.group 5 3206 false)⟩)))))))

theorem tree187_checked : tree187.check 196785 198065 = true := by decide +kernel

def tree188 : Tree := (.branch 198705
(.branch 198385
(.branch 198225
(.branch 198145
(.branch 198105
(.branch 198085
(.leaf ⟨198065,20,(.group 5 3207 false)⟩)
(.leaf ⟨198085,20,(.group 5 3208 false)⟩))
(.branch 198125
(.leaf ⟨198105,20,(.group 5 3209 false)⟩)
(.leaf ⟨198125,20,(.group 5 3210 false)⟩)))
(.branch 198185
(.branch 198165
(.leaf ⟨198145,20,(.group 5 3211 false)⟩)
(.leaf ⟨198165,20,(.group 5 3212 false)⟩))
(.branch 198205
(.leaf ⟨198185,20,(.group 5 3213 false)⟩)
(.leaf ⟨198205,20,(.group 5 3214 false)⟩))))
(.branch 198305
(.branch 198265
(.branch 198245
(.leaf ⟨198225,20,(.group 5 3215 false)⟩)
(.leaf ⟨198245,20,(.group 5 3216 false)⟩))
(.branch 198285
(.leaf ⟨198265,20,(.group 5 3217 false)⟩)
(.leaf ⟨198285,20,(.group 5 3218 false)⟩)))
(.branch 198345
(.branch 198325
(.leaf ⟨198305,20,(.group 5 3219 false)⟩)
(.leaf ⟨198325,20,(.group 5 3220 false)⟩))
(.branch 198365
(.leaf ⟨198345,20,(.group 5 3221 false)⟩)
(.leaf ⟨198365,20,(.group 5 3222 false)⟩)))))
(.branch 198545
(.branch 198465
(.branch 198425
(.branch 198405
(.leaf ⟨198385,20,(.group 5 3223 false)⟩)
(.leaf ⟨198405,20,(.group 5 3224 false)⟩))
(.branch 198445
(.leaf ⟨198425,20,(.group 5 3225 false)⟩)
(.leaf ⟨198445,20,(.group 5 3226 false)⟩)))
(.branch 198505
(.branch 198485
(.leaf ⟨198465,20,(.group 5 3227 false)⟩)
(.leaf ⟨198485,20,(.group 5 3228 false)⟩))
(.branch 198525
(.leaf ⟨198505,20,(.group 5 3229 false)⟩)
(.leaf ⟨198525,20,(.group 5 3230 false)⟩))))
(.branch 198625
(.branch 198585
(.branch 198565
(.leaf ⟨198545,20,(.group 5 3231 false)⟩)
(.leaf ⟨198565,20,(.group 5 3232 false)⟩))
(.branch 198605
(.leaf ⟨198585,20,(.group 5 3233 false)⟩)
(.leaf ⟨198605,20,(.group 5 3234 false)⟩)))
(.branch 198665
(.branch 198645
(.leaf ⟨198625,20,(.group 5 3235 false)⟩)
(.leaf ⟨198645,20,(.group 5 3236 false)⟩))
(.branch 198685
(.leaf ⟨198665,20,(.group 5 3237 false)⟩)
(.leaf ⟨198685,20,(.group 5 3238 false)⟩))))))
(.branch 199025
(.branch 198865
(.branch 198785
(.branch 198745
(.branch 198725
(.leaf ⟨198705,20,(.group 5 3239 false)⟩)
(.leaf ⟨198725,20,(.group 5 3240 false)⟩))
(.branch 198765
(.leaf ⟨198745,20,(.group 5 3241 false)⟩)
(.leaf ⟨198765,20,(.group 5 3242 false)⟩)))
(.branch 198825
(.branch 198805
(.leaf ⟨198785,20,(.group 5 3243 false)⟩)
(.leaf ⟨198805,20,(.group 5 3244 false)⟩))
(.branch 198845
(.leaf ⟨198825,20,(.group 5 3245 false)⟩)
(.leaf ⟨198845,20,(.group 5 3246 false)⟩))))
(.branch 198945
(.branch 198905
(.branch 198885
(.leaf ⟨198865,20,(.group 5 3247 false)⟩)
(.leaf ⟨198885,20,(.group 5 3248 false)⟩))
(.branch 198925
(.leaf ⟨198905,20,(.group 5 3249 false)⟩)
(.leaf ⟨198925,20,(.group 5 3250 false)⟩)))
(.branch 198985
(.branch 198965
(.leaf ⟨198945,20,(.group 5 3251 false)⟩)
(.leaf ⟨198965,20,(.group 5 3252 false)⟩))
(.branch 199005
(.leaf ⟨198985,20,(.group 5 3253 false)⟩)
(.leaf ⟨199005,20,(.group 5 3254 false)⟩)))))
(.branch 199185
(.branch 199105
(.branch 199065
(.branch 199045
(.leaf ⟨199025,20,(.group 5 3255 false)⟩)
(.leaf ⟨199045,20,(.group 5 3256 false)⟩))
(.branch 199085
(.leaf ⟨199065,20,(.group 5 3257 false)⟩)
(.leaf ⟨199085,20,(.group 5 3258 false)⟩)))
(.branch 199145
(.branch 199125
(.leaf ⟨199105,20,(.group 5 3259 false)⟩)
(.leaf ⟨199125,20,(.group 5 3260 false)⟩))
(.branch 199165
(.leaf ⟨199145,20,(.group 5 3261 false)⟩)
(.leaf ⟨199165,20,(.group 5 3262 false)⟩))))
(.branch 199265
(.branch 199225
(.branch 199205
(.leaf ⟨199185,20,(.group 5 3263 false)⟩)
(.leaf ⟨199205,20,(.group 5 3264 false)⟩))
(.branch 199245
(.leaf ⟨199225,20,(.group 5 3265 false)⟩)
(.leaf ⟨199245,20,(.group 5 3266 false)⟩)))
(.branch 199305
(.branch 199285
(.leaf ⟨199265,20,(.group 5 3267 false)⟩)
(.leaf ⟨199285,20,(.group 5 3268 false)⟩))
(.branch 199325
(.leaf ⟨199305,20,(.group 5 3269 false)⟩)
(.leaf ⟨199325,20,(.group 5 3270 false)⟩)))))))

theorem tree188_checked : tree188.check 198065 199345 = true := by decide +kernel

def tree189 : Tree := (.branch 199985
(.branch 199665
(.branch 199505
(.branch 199425
(.branch 199385
(.branch 199365
(.leaf ⟨199345,20,(.group 5 3271 false)⟩)
(.leaf ⟨199365,20,(.group 5 3272 false)⟩))
(.branch 199405
(.leaf ⟨199385,20,(.group 5 3273 false)⟩)
(.leaf ⟨199405,20,(.group 5 3274 false)⟩)))
(.branch 199465
(.branch 199445
(.leaf ⟨199425,20,(.group 5 3275 false)⟩)
(.leaf ⟨199445,20,(.group 5 3276 false)⟩))
(.branch 199485
(.leaf ⟨199465,20,(.group 5 3277 false)⟩)
(.leaf ⟨199485,20,(.group 5 3278 false)⟩))))
(.branch 199585
(.branch 199545
(.branch 199525
(.leaf ⟨199505,20,(.group 5 3279 false)⟩)
(.leaf ⟨199525,20,(.group 5 3280 false)⟩))
(.branch 199565
(.leaf ⟨199545,20,(.group 5 3281 false)⟩)
(.leaf ⟨199565,20,(.group 5 3282 false)⟩)))
(.branch 199625
(.branch 199605
(.leaf ⟨199585,20,(.group 5 3283 false)⟩)
(.leaf ⟨199605,20,(.group 5 3284 false)⟩))
(.branch 199645
(.leaf ⟨199625,20,(.group 5 3285 false)⟩)
(.leaf ⟨199645,20,(.group 5 3286 false)⟩)))))
(.branch 199825
(.branch 199745
(.branch 199705
(.branch 199685
(.leaf ⟨199665,20,(.group 5 3287 false)⟩)
(.leaf ⟨199685,20,(.group 5 3288 false)⟩))
(.branch 199725
(.leaf ⟨199705,20,(.group 5 3289 false)⟩)
(.leaf ⟨199725,20,(.group 5 3290 false)⟩)))
(.branch 199785
(.branch 199765
(.leaf ⟨199745,20,(.group 5 3291 false)⟩)
(.leaf ⟨199765,20,(.group 5 3292 false)⟩))
(.branch 199805
(.leaf ⟨199785,20,(.group 5 3293 false)⟩)
(.leaf ⟨199805,20,(.group 5 3294 false)⟩))))
(.branch 199905
(.branch 199865
(.branch 199845
(.leaf ⟨199825,20,(.group 5 3295 false)⟩)
(.leaf ⟨199845,20,(.group 5 3296 false)⟩))
(.branch 199885
(.leaf ⟨199865,20,(.group 5 3297 false)⟩)
(.leaf ⟨199885,20,(.group 5 3298 false)⟩)))
(.branch 199945
(.branch 199925
(.leaf ⟨199905,20,(.group 5 3299 false)⟩)
(.leaf ⟨199925,20,(.group 5 3300 false)⟩))
(.branch 199965
(.leaf ⟨199945,20,(.group 5 3301 false)⟩)
(.leaf ⟨199965,20,(.group 5 3302 false)⟩))))))
(.branch 200305
(.branch 200145
(.branch 200065
(.branch 200025
(.branch 200005
(.leaf ⟨199985,20,(.group 5 3303 false)⟩)
(.leaf ⟨200005,20,(.group 5 3304 false)⟩))
(.branch 200045
(.leaf ⟨200025,20,(.group 5 3305 false)⟩)
(.leaf ⟨200045,20,(.group 5 3306 false)⟩)))
(.branch 200105
(.branch 200085
(.leaf ⟨200065,20,(.group 5 3307 false)⟩)
(.leaf ⟨200085,20,(.group 5 3308 false)⟩))
(.branch 200125
(.leaf ⟨200105,20,(.group 5 3309 false)⟩)
(.leaf ⟨200125,20,(.group 5 3310 false)⟩))))
(.branch 200225
(.branch 200185
(.branch 200165
(.leaf ⟨200145,20,(.group 5 3311 false)⟩)
(.leaf ⟨200165,20,(.group 5 3312 false)⟩))
(.branch 200205
(.leaf ⟨200185,20,(.group 5 3313 false)⟩)
(.leaf ⟨200205,20,(.group 5 3314 false)⟩)))
(.branch 200265
(.branch 200245
(.leaf ⟨200225,20,(.group 5 3315 false)⟩)
(.leaf ⟨200245,20,(.group 5 3316 false)⟩))
(.branch 200285
(.leaf ⟨200265,20,(.group 5 3317 false)⟩)
(.leaf ⟨200285,20,(.group 5 3318 false)⟩)))))
(.branch 200465
(.branch 200385
(.branch 200345
(.branch 200325
(.leaf ⟨200305,20,(.group 5 3319 false)⟩)
(.leaf ⟨200325,20,(.group 5 3320 false)⟩))
(.branch 200365
(.leaf ⟨200345,20,(.group 5 3321 false)⟩)
(.leaf ⟨200365,20,(.group 5 3322 false)⟩)))
(.branch 200425
(.branch 200405
(.leaf ⟨200385,20,(.group 5 3323 false)⟩)
(.leaf ⟨200405,20,(.group 5 3324 false)⟩))
(.branch 200445
(.leaf ⟨200425,20,(.group 5 3325 false)⟩)
(.leaf ⟨200445,20,(.group 5 3326 false)⟩))))
(.branch 200545
(.branch 200505
(.branch 200485
(.leaf ⟨200465,20,(.group 5 3327 false)⟩)
(.leaf ⟨200485,20,(.group 5 3328 false)⟩))
(.branch 200525
(.leaf ⟨200505,20,(.group 5 3329 false)⟩)
(.leaf ⟨200525,20,(.group 5 3330 false)⟩)))
(.branch 200585
(.branch 200565
(.leaf ⟨200545,20,(.group 5 3331 false)⟩)
(.leaf ⟨200565,20,(.group 5 3332 false)⟩))
(.branch 200605
(.leaf ⟨200585,20,(.group 5 3333 false)⟩)
(.leaf ⟨200605,20,(.group 5 3334 false)⟩)))))))

theorem tree189_checked : tree189.check 199345 200625 = true := by decide +kernel

def tree190 : Tree := (.branch 201265
(.branch 200945
(.branch 200785
(.branch 200705
(.branch 200665
(.branch 200645
(.leaf ⟨200625,20,(.group 5 3335 false)⟩)
(.leaf ⟨200645,20,(.group 5 3336 false)⟩))
(.branch 200685
(.leaf ⟨200665,20,(.group 5 3337 false)⟩)
(.leaf ⟨200685,20,(.group 5 3338 false)⟩)))
(.branch 200745
(.branch 200725
(.leaf ⟨200705,20,(.group 5 3339 false)⟩)
(.leaf ⟨200725,20,(.group 5 3340 false)⟩))
(.branch 200765
(.leaf ⟨200745,20,(.group 5 3341 false)⟩)
(.leaf ⟨200765,20,(.group 5 3342 false)⟩))))
(.branch 200865
(.branch 200825
(.branch 200805
(.leaf ⟨200785,20,(.group 5 3343 false)⟩)
(.leaf ⟨200805,20,(.group 5 3344 false)⟩))
(.branch 200845
(.leaf ⟨200825,20,(.group 5 3345 false)⟩)
(.leaf ⟨200845,20,(.group 5 3346 false)⟩)))
(.branch 200905
(.branch 200885
(.leaf ⟨200865,20,(.group 5 3347 false)⟩)
(.leaf ⟨200885,20,(.group 5 3348 false)⟩))
(.branch 200925
(.leaf ⟨200905,20,(.group 5 3349 false)⟩)
(.leaf ⟨200925,20,(.group 5 3350 false)⟩)))))
(.branch 201105
(.branch 201025
(.branch 200985
(.branch 200965
(.leaf ⟨200945,20,(.group 5 3351 false)⟩)
(.leaf ⟨200965,20,(.group 5 3352 false)⟩))
(.branch 201005
(.leaf ⟨200985,20,(.group 5 3353 false)⟩)
(.leaf ⟨201005,20,(.group 5 3354 false)⟩)))
(.branch 201065
(.branch 201045
(.leaf ⟨201025,20,(.group 5 3355 false)⟩)
(.leaf ⟨201045,20,(.group 5 3356 false)⟩))
(.branch 201085
(.leaf ⟨201065,20,(.group 5 3357 false)⟩)
(.leaf ⟨201085,20,(.group 5 3358 false)⟩))))
(.branch 201185
(.branch 201145
(.branch 201125
(.leaf ⟨201105,20,(.group 5 3359 false)⟩)
(.leaf ⟨201125,20,(.group 5 3360 false)⟩))
(.branch 201165
(.leaf ⟨201145,20,(.group 5 3361 false)⟩)
(.leaf ⟨201165,20,(.group 5 3362 false)⟩)))
(.branch 201225
(.branch 201205
(.leaf ⟨201185,20,(.group 5 3363 false)⟩)
(.leaf ⟨201205,20,(.group 5 3364 false)⟩))
(.branch 201245
(.leaf ⟨201225,20,(.group 5 3365 false)⟩)
(.leaf ⟨201245,20,(.group 5 3366 false)⟩))))))
(.branch 201585
(.branch 201425
(.branch 201345
(.branch 201305
(.branch 201285
(.leaf ⟨201265,20,(.group 5 3367 false)⟩)
(.leaf ⟨201285,20,(.group 5 3368 false)⟩))
(.branch 201325
(.leaf ⟨201305,20,(.group 5 3369 false)⟩)
(.leaf ⟨201325,20,(.group 5 3370 false)⟩)))
(.branch 201385
(.branch 201365
(.leaf ⟨201345,20,(.group 5 3371 false)⟩)
(.leaf ⟨201365,20,(.group 5 3372 false)⟩))
(.branch 201405
(.leaf ⟨201385,20,(.group 5 3373 false)⟩)
(.leaf ⟨201405,20,(.group 5 3374 false)⟩))))
(.branch 201505
(.branch 201465
(.branch 201445
(.leaf ⟨201425,20,(.group 5 3375 false)⟩)
(.leaf ⟨201445,20,(.group 5 3376 false)⟩))
(.branch 201485
(.leaf ⟨201465,20,(.group 5 3377 false)⟩)
(.leaf ⟨201485,20,(.group 5 3378 false)⟩)))
(.branch 201545
(.branch 201525
(.leaf ⟨201505,20,(.group 5 3379 false)⟩)
(.leaf ⟨201525,20,(.group 5 3380 false)⟩))
(.branch 201565
(.leaf ⟨201545,20,(.group 5 3381 false)⟩)
(.leaf ⟨201565,20,(.group 5 3382 false)⟩)))))
(.branch 201745
(.branch 201665
(.branch 201625
(.branch 201605
(.leaf ⟨201585,20,(.group 5 3383 false)⟩)
(.leaf ⟨201605,20,(.group 5 3384 false)⟩))
(.branch 201645
(.leaf ⟨201625,20,(.group 5 3385 false)⟩)
(.leaf ⟨201645,20,(.group 5 3386 false)⟩)))
(.branch 201705
(.branch 201685
(.leaf ⟨201665,20,(.group 5 3387 false)⟩)
(.leaf ⟨201685,20,(.group 5 3388 false)⟩))
(.branch 201725
(.leaf ⟨201705,20,(.group 5 3389 false)⟩)
(.leaf ⟨201725,20,(.group 5 3390 false)⟩))))
(.branch 201825
(.branch 201785
(.branch 201765
(.leaf ⟨201745,20,(.group 5 3391 false)⟩)
(.leaf ⟨201765,20,(.group 5 3392 false)⟩))
(.branch 201805
(.leaf ⟨201785,20,(.group 5 3393 false)⟩)
(.leaf ⟨201805,20,(.group 5 3394 false)⟩)))
(.branch 201865
(.branch 201845
(.leaf ⟨201825,20,(.group 5 3395 false)⟩)
(.leaf ⟨201845,20,(.group 5 3396 false)⟩))
(.branch 201885
(.leaf ⟨201865,20,(.group 5 3397 false)⟩)
(.leaf ⟨201885,20,(.group 5 3398 false)⟩)))))))

theorem tree190_checked : tree190.check 200625 201905 = true := by decide +kernel

def tree191 : Tree := (.branch 202545
(.branch 202225
(.branch 202065
(.branch 201985
(.branch 201945
(.branch 201925
(.leaf ⟨201905,20,(.group 5 3399 false)⟩)
(.leaf ⟨201925,20,(.group 5 3400 false)⟩))
(.branch 201965
(.leaf ⟨201945,20,(.group 5 3401 false)⟩)
(.leaf ⟨201965,20,(.group 5 3402 false)⟩)))
(.branch 202025
(.branch 202005
(.leaf ⟨201985,20,(.group 5 3403 false)⟩)
(.leaf ⟨202005,20,(.group 5 3404 false)⟩))
(.branch 202045
(.leaf ⟨202025,20,(.group 5 3405 false)⟩)
(.leaf ⟨202045,20,(.group 5 3406 false)⟩))))
(.branch 202145
(.branch 202105
(.branch 202085
(.leaf ⟨202065,20,(.group 5 3407 false)⟩)
(.leaf ⟨202085,20,(.group 5 3408 false)⟩))
(.branch 202125
(.leaf ⟨202105,20,(.group 5 3409 false)⟩)
(.leaf ⟨202125,20,(.group 5 3410 false)⟩)))
(.branch 202185
(.branch 202165
(.leaf ⟨202145,20,(.group 5 3411 false)⟩)
(.leaf ⟨202165,20,(.group 5 3412 false)⟩))
(.branch 202205
(.leaf ⟨202185,20,(.group 5 3413 false)⟩)
(.leaf ⟨202205,20,(.group 5 3414 false)⟩)))))
(.branch 202385
(.branch 202305
(.branch 202265
(.branch 202245
(.leaf ⟨202225,20,(.group 5 3415 false)⟩)
(.leaf ⟨202245,20,(.group 5 3416 false)⟩))
(.branch 202285
(.leaf ⟨202265,20,(.group 5 3417 false)⟩)
(.leaf ⟨202285,20,(.group 5 3418 false)⟩)))
(.branch 202345
(.branch 202325
(.leaf ⟨202305,20,(.group 5 3419 false)⟩)
(.leaf ⟨202325,20,(.group 5 3420 false)⟩))
(.branch 202365
(.leaf ⟨202345,20,(.group 5 3421 false)⟩)
(.leaf ⟨202365,20,(.group 5 3422 false)⟩))))
(.branch 202465
(.branch 202425
(.branch 202405
(.leaf ⟨202385,20,(.group 5 3423 false)⟩)
(.leaf ⟨202405,20,(.group 5 3424 false)⟩))
(.branch 202445
(.leaf ⟨202425,20,(.group 5 3425 false)⟩)
(.leaf ⟨202445,20,(.group 5 3426 false)⟩)))
(.branch 202505
(.branch 202485
(.leaf ⟨202465,20,(.group 5 3427 false)⟩)
(.leaf ⟨202485,20,(.group 5 3428 false)⟩))
(.branch 202525
(.leaf ⟨202505,20,(.group 5 3429 false)⟩)
(.leaf ⟨202525,20,(.group 5 3430 false)⟩))))))
(.branch 202865
(.branch 202705
(.branch 202625
(.branch 202585
(.branch 202565
(.leaf ⟨202545,20,(.group 5 3431 false)⟩)
(.leaf ⟨202565,20,(.group 5 3432 false)⟩))
(.branch 202605
(.leaf ⟨202585,20,(.group 5 3433 false)⟩)
(.leaf ⟨202605,20,(.group 5 3434 false)⟩)))
(.branch 202665
(.branch 202645
(.leaf ⟨202625,20,(.group 5 3435 false)⟩)
(.leaf ⟨202645,20,(.group 5 3436 false)⟩))
(.branch 202685
(.leaf ⟨202665,20,(.group 5 3437 false)⟩)
(.leaf ⟨202685,20,(.group 5 3438 false)⟩))))
(.branch 202785
(.branch 202745
(.branch 202725
(.leaf ⟨202705,20,(.group 5 3439 false)⟩)
(.leaf ⟨202725,20,(.group 5 3440 false)⟩))
(.branch 202765
(.leaf ⟨202745,20,(.group 5 3441 false)⟩)
(.leaf ⟨202765,20,(.group 5 3442 false)⟩)))
(.branch 202825
(.branch 202805
(.leaf ⟨202785,20,(.group 5 3443 false)⟩)
(.leaf ⟨202805,20,(.group 5 3444 false)⟩))
(.branch 202845
(.leaf ⟨202825,20,(.group 5 3445 false)⟩)
(.leaf ⟨202845,20,(.group 5 3446 false)⟩)))))
(.branch 203025
(.branch 202945
(.branch 202905
(.branch 202885
(.leaf ⟨202865,20,(.group 5 3447 false)⟩)
(.leaf ⟨202885,20,(.group 5 3448 false)⟩))
(.branch 202925
(.leaf ⟨202905,20,(.group 5 3449 false)⟩)
(.leaf ⟨202925,20,(.group 5 3450 false)⟩)))
(.branch 202985
(.branch 202965
(.leaf ⟨202945,20,(.group 5 3451 false)⟩)
(.leaf ⟨202965,20,(.group 5 3452 false)⟩))
(.branch 203005
(.leaf ⟨202985,20,(.group 5 3453 false)⟩)
(.leaf ⟨203005,20,(.group 5 3454 false)⟩))))
(.branch 203105
(.branch 203065
(.branch 203045
(.leaf ⟨203025,20,(.group 5 3455 false)⟩)
(.leaf ⟨203045,20,(.group 5 3456 false)⟩))
(.branch 203085
(.leaf ⟨203065,20,(.group 5 3457 false)⟩)
(.leaf ⟨203085,20,(.group 5 3458 false)⟩)))
(.branch 203145
(.branch 203125
(.leaf ⟨203105,20,(.group 5 3459 false)⟩)
(.leaf ⟨203125,20,(.group 5 3460 false)⟩))
(.branch 203165
(.leaf ⟨203145,20,(.group 5 3461 false)⟩)
(.leaf ⟨203165,20,(.group 5 3462 false)⟩)))))))

theorem tree191_checked : tree191.check 201905 203185 = true := by decide +kernel

def tree192 : Tree := (.branch 203825
(.branch 203505
(.branch 203345
(.branch 203265
(.branch 203225
(.branch 203205
(.leaf ⟨203185,20,(.group 5 3463 false)⟩)
(.leaf ⟨203205,20,(.group 5 3464 false)⟩))
(.branch 203245
(.leaf ⟨203225,20,(.group 5 3465 false)⟩)
(.leaf ⟨203245,20,(.group 5 3466 false)⟩)))
(.branch 203305
(.branch 203285
(.leaf ⟨203265,20,(.group 5 3467 false)⟩)
(.leaf ⟨203285,20,(.group 5 3468 false)⟩))
(.branch 203325
(.leaf ⟨203305,20,(.group 5 3469 false)⟩)
(.leaf ⟨203325,20,(.group 5 3470 false)⟩))))
(.branch 203425
(.branch 203385
(.branch 203365
(.leaf ⟨203345,20,(.group 5 3471 false)⟩)
(.leaf ⟨203365,20,(.group 5 3472 false)⟩))
(.branch 203405
(.leaf ⟨203385,20,(.group 5 3473 false)⟩)
(.leaf ⟨203405,20,(.group 5 3474 false)⟩)))
(.branch 203465
(.branch 203445
(.leaf ⟨203425,20,(.group 5 3475 false)⟩)
(.leaf ⟨203445,20,(.group 5 3476 false)⟩))
(.branch 203485
(.leaf ⟨203465,20,(.group 5 3477 false)⟩)
(.leaf ⟨203485,20,(.group 5 3478 false)⟩)))))
(.branch 203665
(.branch 203585
(.branch 203545
(.branch 203525
(.leaf ⟨203505,20,(.group 5 3479 false)⟩)
(.leaf ⟨203525,20,(.group 5 3480 false)⟩))
(.branch 203565
(.leaf ⟨203545,20,(.group 5 3481 false)⟩)
(.leaf ⟨203565,20,(.group 5 3482 false)⟩)))
(.branch 203625
(.branch 203605
(.leaf ⟨203585,20,(.group 5 3483 false)⟩)
(.leaf ⟨203605,20,(.group 5 3484 false)⟩))
(.branch 203645
(.leaf ⟨203625,20,(.group 5 3485 false)⟩)
(.leaf ⟨203645,20,(.group 5 3486 false)⟩))))
(.branch 203745
(.branch 203705
(.branch 203685
(.leaf ⟨203665,20,(.group 5 3487 false)⟩)
(.leaf ⟨203685,20,(.group 5 3488 false)⟩))
(.branch 203725
(.leaf ⟨203705,20,(.group 5 3489 false)⟩)
(.leaf ⟨203725,20,(.group 5 3490 false)⟩)))
(.branch 203785
(.branch 203765
(.leaf ⟨203745,20,(.group 5 3491 false)⟩)
(.leaf ⟨203765,20,(.group 5 3492 false)⟩))
(.branch 203805
(.leaf ⟨203785,20,(.group 5 3493 false)⟩)
(.leaf ⟨203805,20,(.group 5 3494 false)⟩))))))
(.branch 204145
(.branch 203985
(.branch 203905
(.branch 203865
(.branch 203845
(.leaf ⟨203825,20,(.group 5 3495 false)⟩)
(.leaf ⟨203845,20,(.group 5 3496 false)⟩))
(.branch 203885
(.leaf ⟨203865,20,(.group 5 3497 false)⟩)
(.leaf ⟨203885,20,(.group 5 3498 false)⟩)))
(.branch 203945
(.branch 203925
(.leaf ⟨203905,20,(.group 5 3499 false)⟩)
(.leaf ⟨203925,20,(.group 5 3500 false)⟩))
(.branch 203965
(.leaf ⟨203945,20,(.group 5 3501 false)⟩)
(.leaf ⟨203965,20,(.group 5 3502 false)⟩))))
(.branch 204065
(.branch 204025
(.branch 204005
(.leaf ⟨203985,20,(.group 5 3503 false)⟩)
(.leaf ⟨204005,20,(.group 5 3504 false)⟩))
(.branch 204045
(.leaf ⟨204025,20,(.group 5 3505 false)⟩)
(.leaf ⟨204045,20,(.group 5 3506 false)⟩)))
(.branch 204105
(.branch 204085
(.leaf ⟨204065,20,(.group 5 3507 false)⟩)
(.leaf ⟨204085,20,(.group 5 3508 false)⟩))
(.branch 204125
(.leaf ⟨204105,20,(.group 5 3509 false)⟩)
(.leaf ⟨204125,20,(.group 5 3510 false)⟩)))))
(.branch 204305
(.branch 204225
(.branch 204185
(.branch 204165
(.leaf ⟨204145,20,(.group 5 3511 false)⟩)
(.leaf ⟨204165,20,(.group 5 3512 false)⟩))
(.branch 204205
(.leaf ⟨204185,20,(.group 5 3513 false)⟩)
(.leaf ⟨204205,20,(.group 5 3514 false)⟩)))
(.branch 204265
(.branch 204245
(.leaf ⟨204225,20,(.group 5 3515 false)⟩)
(.leaf ⟨204245,20,(.group 5 3516 false)⟩))
(.branch 204285
(.leaf ⟨204265,20,(.group 5 3517 false)⟩)
(.leaf ⟨204285,20,(.group 5 3518 false)⟩))))
(.branch 204385
(.branch 204345
(.branch 204325
(.leaf ⟨204305,20,(.group 5 3519 false)⟩)
(.leaf ⟨204325,20,(.group 5 3520 false)⟩))
(.branch 204365
(.leaf ⟨204345,20,(.group 5 3521 false)⟩)
(.leaf ⟨204365,20,(.group 5 3522 false)⟩)))
(.branch 204425
(.branch 204405
(.leaf ⟨204385,20,(.group 5 3523 false)⟩)
(.leaf ⟨204405,20,(.group 5 3524 false)⟩))
(.branch 204445
(.leaf ⟨204425,20,(.group 5 3525 false)⟩)
(.leaf ⟨204445,20,(.group 5 3526 false)⟩)))))))

theorem tree192_checked : tree192.check 203185 204465 = true := by decide +kernel

def tree193 : Tree := (.branch 205105
(.branch 204785
(.branch 204625
(.branch 204545
(.branch 204505
(.branch 204485
(.leaf ⟨204465,20,(.group 5 3527 false)⟩)
(.leaf ⟨204485,20,(.group 5 3528 false)⟩))
(.branch 204525
(.leaf ⟨204505,20,(.group 5 3529 false)⟩)
(.leaf ⟨204525,20,(.group 5 3530 false)⟩)))
(.branch 204585
(.branch 204565
(.leaf ⟨204545,20,(.group 5 3531 false)⟩)
(.leaf ⟨204565,20,(.group 5 3532 false)⟩))
(.branch 204605
(.leaf ⟨204585,20,(.group 5 3533 false)⟩)
(.leaf ⟨204605,20,(.group 5 3534 false)⟩))))
(.branch 204705
(.branch 204665
(.branch 204645
(.leaf ⟨204625,20,(.group 5 3535 false)⟩)
(.leaf ⟨204645,20,(.group 5 3536 false)⟩))
(.branch 204685
(.leaf ⟨204665,20,(.group 5 3537 false)⟩)
(.leaf ⟨204685,20,(.group 5 3538 false)⟩)))
(.branch 204745
(.branch 204725
(.leaf ⟨204705,20,(.group 5 3539 false)⟩)
(.leaf ⟨204725,20,(.group 5 3540 false)⟩))
(.branch 204765
(.leaf ⟨204745,20,(.group 5 3541 false)⟩)
(.leaf ⟨204765,20,(.group 5 3542 false)⟩)))))
(.branch 204945
(.branch 204865
(.branch 204825
(.branch 204805
(.leaf ⟨204785,20,(.group 5 3543 false)⟩)
(.leaf ⟨204805,20,(.group 5 3544 false)⟩))
(.branch 204845
(.leaf ⟨204825,20,(.group 5 3545 false)⟩)
(.leaf ⟨204845,20,(.group 5 3546 false)⟩)))
(.branch 204905
(.branch 204885
(.leaf ⟨204865,20,(.group 5 3547 false)⟩)
(.leaf ⟨204885,20,(.group 5 3548 false)⟩))
(.branch 204925
(.leaf ⟨204905,20,(.group 5 3549 false)⟩)
(.leaf ⟨204925,20,(.group 5 3550 false)⟩))))
(.branch 205025
(.branch 204985
(.branch 204965
(.leaf ⟨204945,20,(.group 5 3551 false)⟩)
(.leaf ⟨204965,20,(.group 5 3552 false)⟩))
(.branch 205005
(.leaf ⟨204985,20,(.group 5 3553 false)⟩)
(.leaf ⟨205005,20,(.group 5 3554 false)⟩)))
(.branch 205065
(.branch 205045
(.leaf ⟨205025,20,(.group 5 3555 false)⟩)
(.leaf ⟨205045,20,(.group 5 3556 false)⟩))
(.branch 205085
(.leaf ⟨205065,20,(.group 5 3557 false)⟩)
(.leaf ⟨205085,20,(.group 5 3558 false)⟩))))))
(.branch 205425
(.branch 205265
(.branch 205185
(.branch 205145
(.branch 205125
(.leaf ⟨205105,20,(.group 5 3559 false)⟩)
(.leaf ⟨205125,20,(.group 5 3560 false)⟩))
(.branch 205165
(.leaf ⟨205145,20,(.group 5 3561 false)⟩)
(.leaf ⟨205165,20,(.group 5 3562 false)⟩)))
(.branch 205225
(.branch 205205
(.leaf ⟨205185,20,(.group 5 3563 false)⟩)
(.leaf ⟨205205,20,(.group 5 3564 false)⟩))
(.branch 205245
(.leaf ⟨205225,20,(.group 5 3565 false)⟩)
(.leaf ⟨205245,20,(.group 5 3566 false)⟩))))
(.branch 205345
(.branch 205305
(.branch 205285
(.leaf ⟨205265,20,(.group 5 3567 false)⟩)
(.leaf ⟨205285,20,(.group 5 3568 false)⟩))
(.branch 205325
(.leaf ⟨205305,20,(.group 5 3569 false)⟩)
(.leaf ⟨205325,20,(.group 5 3570 false)⟩)))
(.branch 205385
(.branch 205365
(.leaf ⟨205345,20,(.group 5 3571 false)⟩)
(.leaf ⟨205365,20,(.group 5 3572 false)⟩))
(.branch 205405
(.leaf ⟨205385,20,(.group 5 3573 false)⟩)
(.leaf ⟨205405,20,(.group 7 488 false)⟩)))))
(.branch 205585
(.branch 205505
(.branch 205465
(.branch 205445
(.leaf ⟨205425,20,(.group 7 489 false)⟩)
(.leaf ⟨205445,20,(.group 7 490 false)⟩))
(.branch 205485
(.leaf ⟨205465,20,(.group 7 491 false)⟩)
(.leaf ⟨205485,20,(.group 7 492 false)⟩)))
(.branch 205545
(.branch 205525
(.leaf ⟨205505,20,(.group 7 493 false)⟩)
(.leaf ⟨205525,20,(.group 7 494 false)⟩))
(.branch 205565
(.leaf ⟨205545,20,(.group 7 495 false)⟩)
(.leaf ⟨205565,20,(.group 7 496 false)⟩))))
(.branch 205665
(.branch 205625
(.branch 205605
(.leaf ⟨205585,20,(.group 7 497 false)⟩)
(.leaf ⟨205605,20,(.group 7 498 false)⟩))
(.branch 205645
(.leaf ⟨205625,20,(.group 7 499 false)⟩)
(.leaf ⟨205645,20,(.group 7 500 false)⟩)))
(.branch 205705
(.branch 205685
(.leaf ⟨205665,20,(.group 7 501 false)⟩)
(.leaf ⟨205685,20,(.group 7 502 false)⟩))
(.branch 205725
(.leaf ⟨205705,20,(.group 7 503 false)⟩)
(.leaf ⟨205725,20,(.group 7 504 false)⟩)))))))

theorem tree193_checked : tree193.check 204465 205745 = true := by decide +kernel

def tree194 : Tree := (.branch 206385
(.branch 206065
(.branch 205905
(.branch 205825
(.branch 205785
(.branch 205765
(.leaf ⟨205745,20,(.group 7 505 false)⟩)
(.leaf ⟨205765,20,(.group 7 506 false)⟩))
(.branch 205805
(.leaf ⟨205785,20,(.group 7 507 false)⟩)
(.leaf ⟨205805,20,(.group 7 508 false)⟩)))
(.branch 205865
(.branch 205845
(.leaf ⟨205825,20,(.group 7 509 false)⟩)
(.leaf ⟨205845,20,(.group 7 510 false)⟩))
(.branch 205885
(.leaf ⟨205865,20,(.group 7 511 false)⟩)
(.leaf ⟨205885,20,(.group 7 512 false)⟩))))
(.branch 205985
(.branch 205945
(.branch 205925
(.leaf ⟨205905,20,(.group 7 513 false)⟩)
(.leaf ⟨205925,20,(.group 7 514 false)⟩))
(.branch 205965
(.leaf ⟨205945,20,(.group 7 515 false)⟩)
(.leaf ⟨205965,20,(.group 7 516 false)⟩)))
(.branch 206025
(.branch 206005
(.leaf ⟨205985,20,(.group 7 517 false)⟩)
(.leaf ⟨206005,20,(.group 7 518 false)⟩))
(.branch 206045
(.leaf ⟨206025,20,(.group 7 519 false)⟩)
(.leaf ⟨206045,20,(.group 7 520 false)⟩)))))
(.branch 206225
(.branch 206145
(.branch 206105
(.branch 206085
(.leaf ⟨206065,20,(.group 7 521 false)⟩)
(.leaf ⟨206085,20,(.group 7 522 false)⟩))
(.branch 206125
(.leaf ⟨206105,20,(.group 7 523 false)⟩)
(.leaf ⟨206125,20,(.group 7 524 false)⟩)))
(.branch 206185
(.branch 206165
(.leaf ⟨206145,20,(.group 7 525 false)⟩)
(.leaf ⟨206165,20,(.group 7 526 false)⟩))
(.branch 206205
(.leaf ⟨206185,20,(.group 7 527 false)⟩)
(.leaf ⟨206205,20,(.group 7 528 false)⟩))))
(.branch 206305
(.branch 206265
(.branch 206245
(.leaf ⟨206225,20,(.group 7 529 false)⟩)
(.leaf ⟨206245,20,(.group 7 530 false)⟩))
(.branch 206285
(.leaf ⟨206265,20,(.group 7 531 false)⟩)
(.leaf ⟨206285,20,(.group 7 532 false)⟩)))
(.branch 206345
(.branch 206325
(.leaf ⟨206305,20,(.group 7 533 false)⟩)
(.leaf ⟨206325,20,(.group 7 534 false)⟩))
(.branch 206365
(.leaf ⟨206345,20,(.group 7 535 false)⟩)
(.leaf ⟨206365,20,(.group 7 536 false)⟩))))))
(.branch 206705
(.branch 206545
(.branch 206465
(.branch 206425
(.branch 206405
(.leaf ⟨206385,20,(.group 7 537 false)⟩)
(.leaf ⟨206405,20,(.group 7 538 false)⟩))
(.branch 206445
(.leaf ⟨206425,20,(.group 7 539 false)⟩)
(.leaf ⟨206445,20,(.group 7 540 false)⟩)))
(.branch 206505
(.branch 206485
(.leaf ⟨206465,20,(.group 7 541 false)⟩)
(.leaf ⟨206485,20,(.group 7 542 false)⟩))
(.branch 206525
(.leaf ⟨206505,20,(.group 7 543 false)⟩)
(.leaf ⟨206525,20,(.group 7 544 false)⟩))))
(.branch 206625
(.branch 206585
(.branch 206565
(.leaf ⟨206545,20,(.group 7 545 false)⟩)
(.leaf ⟨206565,20,(.group 7 546 false)⟩))
(.branch 206605
(.leaf ⟨206585,20,(.group 7 547 false)⟩)
(.leaf ⟨206605,20,(.group 7 548 false)⟩)))
(.branch 206665
(.branch 206645
(.leaf ⟨206625,20,(.group 7 549 false)⟩)
(.leaf ⟨206645,20,(.group 7 550 false)⟩))
(.branch 206685
(.leaf ⟨206665,20,(.group 7 551 false)⟩)
(.leaf ⟨206685,20,(.group 7 552 false)⟩)))))
(.branch 206865
(.branch 206785
(.branch 206745
(.branch 206725
(.leaf ⟨206705,20,(.group 7 553 false)⟩)
(.leaf ⟨206725,20,(.group 7 554 false)⟩))
(.branch 206765
(.leaf ⟨206745,20,(.group 7 555 false)⟩)
(.leaf ⟨206765,20,(.group 7 556 false)⟩)))
(.branch 206825
(.branch 206805
(.leaf ⟨206785,20,(.group 7 557 false)⟩)
(.leaf ⟨206805,20,(.group 7 558 false)⟩))
(.branch 206845
(.leaf ⟨206825,20,(.group 7 559 false)⟩)
(.leaf ⟨206845,20,(.group 7 560 false)⟩))))
(.branch 206945
(.branch 206905
(.branch 206885
(.leaf ⟨206865,20,(.group 7 561 false)⟩)
(.leaf ⟨206885,20,(.group 7 562 false)⟩))
(.branch 206925
(.leaf ⟨206905,20,(.group 7 563 false)⟩)
(.leaf ⟨206925,20,(.group 7 564 false)⟩)))
(.branch 206985
(.branch 206965
(.leaf ⟨206945,20,(.group 7 565 false)⟩)
(.leaf ⟨206965,20,(.group 7 566 false)⟩))
(.branch 207005
(.leaf ⟨206985,20,(.group 7 567 false)⟩)
(.leaf ⟨207005,20,(.group 7 568 false)⟩)))))))

theorem tree194_checked : tree194.check 205745 207025 = true := by decide +kernel

def tree195 : Tree := (.branch 207665
(.branch 207345
(.branch 207185
(.branch 207105
(.branch 207065
(.branch 207045
(.leaf ⟨207025,20,(.group 7 569 false)⟩)
(.leaf ⟨207045,20,(.group 7 570 false)⟩))
(.branch 207085
(.leaf ⟨207065,20,(.group 7 571 false)⟩)
(.leaf ⟨207085,20,(.group 7 572 false)⟩)))
(.branch 207145
(.branch 207125
(.leaf ⟨207105,20,(.group 7 573 false)⟩)
(.leaf ⟨207125,20,(.group 7 574 false)⟩))
(.branch 207165
(.leaf ⟨207145,20,(.group 7 575 false)⟩)
(.leaf ⟨207165,20,(.group 7 576 false)⟩))))
(.branch 207265
(.branch 207225
(.branch 207205
(.leaf ⟨207185,20,(.group 7 577 false)⟩)
(.leaf ⟨207205,20,(.group 7 578 false)⟩))
(.branch 207245
(.leaf ⟨207225,20,(.group 7 579 false)⟩)
(.leaf ⟨207245,20,(.group 7 580 false)⟩)))
(.branch 207305
(.branch 207285
(.leaf ⟨207265,20,(.group 7 581 false)⟩)
(.leaf ⟨207285,20,(.group 7 582 false)⟩))
(.branch 207325
(.leaf ⟨207305,20,(.group 7 583 false)⟩)
(.leaf ⟨207325,20,(.group 7 584 false)⟩)))))
(.branch 207505
(.branch 207425
(.branch 207385
(.branch 207365
(.leaf ⟨207345,20,(.group 7 585 false)⟩)
(.leaf ⟨207365,20,(.group 7 586 false)⟩))
(.branch 207405
(.leaf ⟨207385,20,(.group 7 587 false)⟩)
(.leaf ⟨207405,20,(.group 7 588 false)⟩)))
(.branch 207465
(.branch 207445
(.leaf ⟨207425,20,(.group 7 589 false)⟩)
(.leaf ⟨207445,20,(.group 7 590 false)⟩))
(.branch 207485
(.leaf ⟨207465,20,(.group 7 591 false)⟩)
(.leaf ⟨207485,20,(.group 7 592 false)⟩))))
(.branch 207585
(.branch 207545
(.branch 207525
(.leaf ⟨207505,20,(.group 8 600 false)⟩)
(.leaf ⟨207525,20,(.group 8 601 false)⟩))
(.branch 207565
(.leaf ⟨207545,20,(.group 8 602 false)⟩)
(.leaf ⟨207565,20,(.group 8 603 false)⟩)))
(.branch 207625
(.branch 207605
(.leaf ⟨207585,20,(.group 8 604 false)⟩)
(.leaf ⟨207605,20,(.group 8 605 false)⟩))
(.branch 207645
(.leaf ⟨207625,20,(.group 8 606 false)⟩)
(.leaf ⟨207645,20,(.group 8 607 false)⟩))))))
(.branch 207985
(.branch 207825
(.branch 207745
(.branch 207705
(.branch 207685
(.leaf ⟨207665,20,(.group 8 608 false)⟩)
(.leaf ⟨207685,20,(.group 8 609 false)⟩))
(.branch 207725
(.leaf ⟨207705,20,(.group 8 610 false)⟩)
(.leaf ⟨207725,20,(.group 8 611 false)⟩)))
(.branch 207785
(.branch 207765
(.leaf ⟨207745,20,(.group 8 612 false)⟩)
(.leaf ⟨207765,20,(.group 8 613 false)⟩))
(.branch 207805
(.leaf ⟨207785,20,(.group 8 614 false)⟩)
(.leaf ⟨207805,20,(.group 8 615 false)⟩))))
(.branch 207905
(.branch 207865
(.branch 207845
(.leaf ⟨207825,20,(.group 8 616 false)⟩)
(.leaf ⟨207845,20,(.group 8 617 false)⟩))
(.branch 207885
(.leaf ⟨207865,20,(.group 8 618 false)⟩)
(.leaf ⟨207885,20,(.group 8 619 false)⟩)))
(.branch 207945
(.branch 207925
(.leaf ⟨207905,20,(.group 8 620 false)⟩)
(.leaf ⟨207925,20,(.group 8 621 false)⟩))
(.branch 207965
(.leaf ⟨207945,20,(.group 8 622 false)⟩)
(.leaf ⟨207965,20,(.group 8 623 false)⟩)))))
(.branch 208153
(.branch 208069
(.branch 208027
(.branch 208006
(.leaf ⟨207985,21,(.group 5 3574 false)⟩)
(.leaf ⟨208006,21,(.group 5 3575 false)⟩))
(.branch 208048
(.leaf ⟨208027,21,(.group 5 3576 false)⟩)
(.leaf ⟨208048,21,(.group 5 3577 false)⟩)))
(.branch 208111
(.branch 208090
(.leaf ⟨208069,21,(.group 5 3578 false)⟩)
(.leaf ⟨208090,21,(.group 5 3579 false)⟩))
(.branch 208132
(.leaf ⟨208111,21,(.group 5 3580 false)⟩)
(.leaf ⟨208132,21,(.group 5 3581 false)⟩))))
(.branch 208237
(.branch 208195
(.branch 208174
(.leaf ⟨208153,21,(.group 5 3582 false)⟩)
(.leaf ⟨208174,21,(.group 5 3583 false)⟩))
(.branch 208216
(.leaf ⟨208195,21,(.group 5 3584 false)⟩)
(.leaf ⟨208216,21,(.group 5 3585 false)⟩)))
(.branch 208279
(.branch 208258
(.leaf ⟨208237,21,(.group 5 3586 false)⟩)
(.leaf ⟨208258,21,(.group 5 3587 false)⟩))
(.branch 208300
(.leaf ⟨208279,21,(.group 5 3588 false)⟩)
(.leaf ⟨208300,21,(.group 5 3589 false)⟩)))))))

theorem tree195_checked : tree195.check 207025 208321 = true := by decide +kernel

def tree196 : Tree := (.branch 208993
(.branch 208657
(.branch 208489
(.branch 208405
(.branch 208363
(.branch 208342
(.leaf ⟨208321,21,(.group 5 3590 false)⟩)
(.leaf ⟨208342,21,(.group 5 3591 false)⟩))
(.branch 208384
(.leaf ⟨208363,21,(.group 5 3592 false)⟩)
(.leaf ⟨208384,21,(.group 5 3593 false)⟩)))
(.branch 208447
(.branch 208426
(.leaf ⟨208405,21,(.group 5 3594 false)⟩)
(.leaf ⟨208426,21,(.group 5 3595 false)⟩))
(.branch 208468
(.leaf ⟨208447,21,(.group 5 3596 false)⟩)
(.leaf ⟨208468,21,(.group 5 3597 false)⟩))))
(.branch 208573
(.branch 208531
(.branch 208510
(.leaf ⟨208489,21,(.group 5 3598 false)⟩)
(.leaf ⟨208510,21,(.group 5 3599 false)⟩))
(.branch 208552
(.leaf ⟨208531,21,(.group 5 3600 false)⟩)
(.leaf ⟨208552,21,(.group 5 3601 false)⟩)))
(.branch 208615
(.branch 208594
(.leaf ⟨208573,21,(.group 5 3602 false)⟩)
(.leaf ⟨208594,21,(.group 5 3603 false)⟩))
(.branch 208636
(.leaf ⟨208615,21,(.group 5 3604 false)⟩)
(.leaf ⟨208636,21,(.group 5 3605 false)⟩)))))
(.branch 208825
(.branch 208741
(.branch 208699
(.branch 208678
(.leaf ⟨208657,21,(.group 5 3606 false)⟩)
(.leaf ⟨208678,21,(.group 5 3607 false)⟩))
(.branch 208720
(.leaf ⟨208699,21,(.group 5 3608 false)⟩)
(.leaf ⟨208720,21,(.group 5 3609 false)⟩)))
(.branch 208783
(.branch 208762
(.leaf ⟨208741,21,(.group 5 3610 false)⟩)
(.leaf ⟨208762,21,(.group 5 3611 false)⟩))
(.branch 208804
(.leaf ⟨208783,21,(.group 5 3612 false)⟩)
(.leaf ⟨208804,21,(.group 5 3613 false)⟩))))
(.branch 208909
(.branch 208867
(.branch 208846
(.leaf ⟨208825,21,(.group 5 3614 false)⟩)
(.leaf ⟨208846,21,(.group 5 3615 false)⟩))
(.branch 208888
(.leaf ⟨208867,21,(.group 5 3616 false)⟩)
(.leaf ⟨208888,21,(.group 5 3617 false)⟩)))
(.branch 208951
(.branch 208930
(.leaf ⟨208909,21,(.group 5 3618 false)⟩)
(.leaf ⟨208930,21,(.group 5 3619 false)⟩))
(.branch 208972
(.leaf ⟨208951,21,(.group 5 3620 false)⟩)
(.leaf ⟨208972,21,(.group 5 3621 false)⟩))))))
(.branch 209329
(.branch 209161
(.branch 209077
(.branch 209035
(.branch 209014
(.leaf ⟨208993,21,(.group 5 3622 false)⟩)
(.leaf ⟨209014,21,(.group 5 3623 false)⟩))
(.branch 209056
(.leaf ⟨209035,21,(.group 5 3624 false)⟩)
(.leaf ⟨209056,21,(.group 5 3625 false)⟩)))
(.branch 209119
(.branch 209098
(.leaf ⟨209077,21,(.group 5 3626 false)⟩)
(.leaf ⟨209098,21,(.group 5 3627 false)⟩))
(.branch 209140
(.leaf ⟨209119,21,(.group 5 3628 false)⟩)
(.leaf ⟨209140,21,(.group 5 3629 false)⟩))))
(.branch 209245
(.branch 209203
(.branch 209182
(.leaf ⟨209161,21,(.group 5 3630 false)⟩)
(.leaf ⟨209182,21,(.group 5 3631 false)⟩))
(.branch 209224
(.leaf ⟨209203,21,(.group 5 3632 false)⟩)
(.leaf ⟨209224,21,(.group 5 3633 false)⟩)))
(.branch 209287
(.branch 209266
(.leaf ⟨209245,21,(.group 5 3634 false)⟩)
(.leaf ⟨209266,21,(.group 5 3635 false)⟩))
(.branch 209308
(.leaf ⟨209287,21,(.group 5 3636 false)⟩)
(.leaf ⟨209308,21,(.group 5 3637 false)⟩)))))
(.branch 209497
(.branch 209413
(.branch 209371
(.branch 209350
(.leaf ⟨209329,21,(.group 5 3638 false)⟩)
(.leaf ⟨209350,21,(.group 5 3639 false)⟩))
(.branch 209392
(.leaf ⟨209371,21,(.group 5 3640 false)⟩)
(.leaf ⟨209392,21,(.group 5 3641 false)⟩)))
(.branch 209455
(.branch 209434
(.leaf ⟨209413,21,(.group 5 3642 false)⟩)
(.leaf ⟨209434,21,(.group 5 3643 false)⟩))
(.branch 209476
(.leaf ⟨209455,21,(.group 5 3644 false)⟩)
(.leaf ⟨209476,21,(.group 5 3645 false)⟩))))
(.branch 209581
(.branch 209539
(.branch 209518
(.leaf ⟨209497,21,(.group 5 3646 false)⟩)
(.leaf ⟨209518,21,(.group 5 3647 false)⟩))
(.branch 209560
(.leaf ⟨209539,21,(.group 5 3648 false)⟩)
(.leaf ⟨209560,21,(.group 5 3649 false)⟩)))
(.branch 209623
(.branch 209602
(.leaf ⟨209581,21,(.group 5 3650 false)⟩)
(.leaf ⟨209602,21,(.group 5 3651 false)⟩))
(.branch 209644
(.leaf ⟨209623,21,(.group 5 3652 false)⟩)
(.leaf ⟨209644,21,(.group 5 3653 false)⟩)))))))

theorem tree196_checked : tree196.check 208321 209665 = true := by decide +kernel

def tree197 : Tree := (.branch 210337
(.branch 210001
(.branch 209833
(.branch 209749
(.branch 209707
(.branch 209686
(.leaf ⟨209665,21,(.group 5 3654 false)⟩)
(.leaf ⟨209686,21,(.group 5 3655 false)⟩))
(.branch 209728
(.leaf ⟨209707,21,(.group 5 3656 false)⟩)
(.leaf ⟨209728,21,(.group 5 3657 false)⟩)))
(.branch 209791
(.branch 209770
(.leaf ⟨209749,21,(.group 5 3658 false)⟩)
(.leaf ⟨209770,21,(.group 5 3659 false)⟩))
(.branch 209812
(.leaf ⟨209791,21,(.group 5 3660 false)⟩)
(.leaf ⟨209812,21,(.group 5 3661 false)⟩))))
(.branch 209917
(.branch 209875
(.branch 209854
(.leaf ⟨209833,21,(.group 5 3662 false)⟩)
(.leaf ⟨209854,21,(.group 5 3663 false)⟩))
(.branch 209896
(.leaf ⟨209875,21,(.group 5 3664 false)⟩)
(.leaf ⟨209896,21,(.group 5 3665 false)⟩)))
(.branch 209959
(.branch 209938
(.leaf ⟨209917,21,(.group 5 3666 false)⟩)
(.leaf ⟨209938,21,(.group 5 3667 false)⟩))
(.branch 209980
(.leaf ⟨209959,21,(.group 5 3668 false)⟩)
(.leaf ⟨209980,21,(.group 5 3669 false)⟩)))))
(.branch 210169
(.branch 210085
(.branch 210043
(.branch 210022
(.leaf ⟨210001,21,(.group 5 3670 false)⟩)
(.leaf ⟨210022,21,(.group 5 3671 false)⟩))
(.branch 210064
(.leaf ⟨210043,21,(.group 5 3672 false)⟩)
(.leaf ⟨210064,21,(.group 5 3673 false)⟩)))
(.branch 210127
(.branch 210106
(.leaf ⟨210085,21,(.group 5 3674 false)⟩)
(.leaf ⟨210106,21,(.group 5 3675 false)⟩))
(.branch 210148
(.leaf ⟨210127,21,(.group 5 3676 false)⟩)
(.leaf ⟨210148,21,(.group 5 3677 false)⟩))))
(.branch 210253
(.branch 210211
(.branch 210190
(.leaf ⟨210169,21,(.group 5 3678 false)⟩)
(.leaf ⟨210190,21,(.group 5 3679 false)⟩))
(.branch 210232
(.leaf ⟨210211,21,(.group 5 3680 false)⟩)
(.leaf ⟨210232,21,(.group 5 3681 false)⟩)))
(.branch 210295
(.branch 210274
(.leaf ⟨210253,21,(.group 5 3682 false)⟩)
(.leaf ⟨210274,21,(.group 5 3683 false)⟩))
(.branch 210316
(.leaf ⟨210295,21,(.group 5 3684 false)⟩)
(.leaf ⟨210316,21,(.group 5 3685 false)⟩))))))
(.branch 210673
(.branch 210505
(.branch 210421
(.branch 210379
(.branch 210358
(.leaf ⟨210337,21,(.group 5 3686 false)⟩)
(.leaf ⟨210358,21,(.group 5 3687 false)⟩))
(.branch 210400
(.leaf ⟨210379,21,(.group 5 3688 false)⟩)
(.leaf ⟨210400,21,(.group 5 3689 false)⟩)))
(.branch 210463
(.branch 210442
(.leaf ⟨210421,21,(.group 5 3690 false)⟩)
(.leaf ⟨210442,21,(.group 5 3691 false)⟩))
(.branch 210484
(.leaf ⟨210463,21,(.group 5 3692 false)⟩)
(.leaf ⟨210484,21,(.group 5 3693 false)⟩))))
(.branch 210589
(.branch 210547
(.branch 210526
(.leaf ⟨210505,21,(.group 5 3694 false)⟩)
(.leaf ⟨210526,21,(.group 5 3695 false)⟩))
(.branch 210568
(.leaf ⟨210547,21,(.group 5 3696 false)⟩)
(.leaf ⟨210568,21,(.group 5 3697 false)⟩)))
(.branch 210631
(.branch 210610
(.leaf ⟨210589,21,(.group 5 3698 false)⟩)
(.leaf ⟨210610,21,(.group 5 3699 false)⟩))
(.branch 210652
(.leaf ⟨210631,21,(.group 5 3700 false)⟩)
(.leaf ⟨210652,21,(.group 5 3701 false)⟩)))))
(.branch 210841
(.branch 210757
(.branch 210715
(.branch 210694
(.leaf ⟨210673,21,(.group 5 3702 false)⟩)
(.leaf ⟨210694,21,(.group 5 3703 false)⟩))
(.branch 210736
(.leaf ⟨210715,21,(.group 5 3704 false)⟩)
(.leaf ⟨210736,21,(.group 5 3705 false)⟩)))
(.branch 210799
(.branch 210778
(.leaf ⟨210757,21,(.group 5 3706 false)⟩)
(.leaf ⟨210778,21,(.group 5 3707 false)⟩))
(.branch 210820
(.leaf ⟨210799,21,(.group 5 3708 false)⟩)
(.leaf ⟨210820,21,(.group 5 3709 false)⟩))))
(.branch 210925
(.branch 210883
(.branch 210862
(.leaf ⟨210841,21,(.group 5 3710 false)⟩)
(.leaf ⟨210862,21,(.group 5 3711 false)⟩))
(.branch 210904
(.leaf ⟨210883,21,(.group 5 3712 false)⟩)
(.leaf ⟨210904,21,(.group 5 3713 false)⟩)))
(.branch 210967
(.branch 210946
(.leaf ⟨210925,21,(.group 5 3714 false)⟩)
(.leaf ⟨210946,21,(.group 5 3715 false)⟩))
(.branch 210988
(.leaf ⟨210967,21,(.group 5 3716 false)⟩)
(.leaf ⟨210988,21,(.group 5 3717 false)⟩)))))))

theorem tree197_checked : tree197.check 209665 211009 = true := by decide +kernel

def tree198 : Tree := (.branch 211681
(.branch 211345
(.branch 211177
(.branch 211093
(.branch 211051
(.branch 211030
(.leaf ⟨211009,21,(.group 5 3718 false)⟩)
(.leaf ⟨211030,21,(.group 5 3719 false)⟩))
(.branch 211072
(.leaf ⟨211051,21,(.group 5 3720 false)⟩)
(.leaf ⟨211072,21,(.group 5 3721 false)⟩)))
(.branch 211135
(.branch 211114
(.leaf ⟨211093,21,(.group 5 3722 false)⟩)
(.leaf ⟨211114,21,(.group 5 3723 false)⟩))
(.branch 211156
(.leaf ⟨211135,21,(.group 5 3724 false)⟩)
(.leaf ⟨211156,21,(.group 5 3725 false)⟩))))
(.branch 211261
(.branch 211219
(.branch 211198
(.leaf ⟨211177,21,(.group 5 3726 false)⟩)
(.leaf ⟨211198,21,(.group 5 3727 false)⟩))
(.branch 211240
(.leaf ⟨211219,21,(.group 5 3728 false)⟩)
(.leaf ⟨211240,21,(.group 5 3729 false)⟩)))
(.branch 211303
(.branch 211282
(.leaf ⟨211261,21,(.group 5 3730 false)⟩)
(.leaf ⟨211282,21,(.group 5 3731 false)⟩))
(.branch 211324
(.leaf ⟨211303,21,(.group 5 3732 false)⟩)
(.leaf ⟨211324,21,(.group 5 3733 false)⟩)))))
(.branch 211513
(.branch 211429
(.branch 211387
(.branch 211366
(.leaf ⟨211345,21,(.group 5 3734 false)⟩)
(.leaf ⟨211366,21,(.group 5 3735 false)⟩))
(.branch 211408
(.leaf ⟨211387,21,(.group 5 3736 false)⟩)
(.leaf ⟨211408,21,(.group 5 3737 false)⟩)))
(.branch 211471
(.branch 211450
(.leaf ⟨211429,21,(.group 5 3738 false)⟩)
(.leaf ⟨211450,21,(.group 5 3739 false)⟩))
(.branch 211492
(.leaf ⟨211471,21,(.group 5 3740 false)⟩)
(.leaf ⟨211492,21,(.group 5 3741 false)⟩))))
(.branch 211597
(.branch 211555
(.branch 211534
(.leaf ⟨211513,21,(.group 5 3742 false)⟩)
(.leaf ⟨211534,21,(.group 5 3743 false)⟩))
(.branch 211576
(.leaf ⟨211555,21,(.group 5 3744 false)⟩)
(.leaf ⟨211576,21,(.group 5 3745 false)⟩)))
(.branch 211639
(.branch 211618
(.leaf ⟨211597,21,(.group 5 3746 false)⟩)
(.leaf ⟨211618,21,(.group 5 3747 false)⟩))
(.branch 211660
(.leaf ⟨211639,21,(.group 5 3748 false)⟩)
(.leaf ⟨211660,21,(.group 5 3749 false)⟩))))))
(.branch 212017
(.branch 211849
(.branch 211765
(.branch 211723
(.branch 211702
(.leaf ⟨211681,21,(.group 5 3750 false)⟩)
(.leaf ⟨211702,21,(.group 5 3751 false)⟩))
(.branch 211744
(.leaf ⟨211723,21,(.group 5 3752 false)⟩)
(.leaf ⟨211744,21,(.group 5 3753 false)⟩)))
(.branch 211807
(.branch 211786
(.leaf ⟨211765,21,(.group 5 3754 false)⟩)
(.leaf ⟨211786,21,(.group 5 3755 false)⟩))
(.branch 211828
(.leaf ⟨211807,21,(.group 5 3756 false)⟩)
(.leaf ⟨211828,21,(.group 5 3757 false)⟩))))
(.branch 211933
(.branch 211891
(.branch 211870
(.leaf ⟨211849,21,(.group 5 3758 false)⟩)
(.leaf ⟨211870,21,(.group 5 3759 false)⟩))
(.branch 211912
(.leaf ⟨211891,21,(.group 5 3760 false)⟩)
(.leaf ⟨211912,21,(.group 5 3761 false)⟩)))
(.branch 211975
(.branch 211954
(.leaf ⟨211933,21,(.group 5 3762 false)⟩)
(.leaf ⟨211954,21,(.group 5 3763 false)⟩))
(.branch 211996
(.leaf ⟨211975,21,(.group 5 3764 false)⟩)
(.leaf ⟨211996,21,(.group 5 3765 false)⟩)))))
(.branch 212185
(.branch 212101
(.branch 212059
(.branch 212038
(.leaf ⟨212017,21,(.group 5 3766 false)⟩)
(.leaf ⟨212038,21,(.group 5 3767 false)⟩))
(.branch 212080
(.leaf ⟨212059,21,(.group 5 3768 false)⟩)
(.leaf ⟨212080,21,(.group 5 3769 false)⟩)))
(.branch 212143
(.branch 212122
(.leaf ⟨212101,21,(.group 5 3770 false)⟩)
(.leaf ⟨212122,21,(.group 5 3771 false)⟩))
(.branch 212164
(.leaf ⟨212143,21,(.group 5 3772 false)⟩)
(.leaf ⟨212164,21,(.group 5 3773 false)⟩))))
(.branch 212269
(.branch 212227
(.branch 212206
(.leaf ⟨212185,21,(.group 5 3774 false)⟩)
(.leaf ⟨212206,21,(.group 5 3775 false)⟩))
(.branch 212248
(.leaf ⟨212227,21,(.group 5 3776 false)⟩)
(.leaf ⟨212248,21,(.group 5 3777 false)⟩)))
(.branch 212311
(.branch 212290
(.leaf ⟨212269,21,(.group 5 3778 false)⟩)
(.leaf ⟨212290,21,(.group 5 3779 false)⟩))
(.branch 212332
(.leaf ⟨212311,21,(.group 5 3780 false)⟩)
(.leaf ⟨212332,21,(.group 5 3781 false)⟩)))))))

theorem tree198_checked : tree198.check 211009 212353 = true := by decide +kernel

def tree199 : Tree := (.branch 213025
(.branch 212689
(.branch 212521
(.branch 212437
(.branch 212395
(.branch 212374
(.leaf ⟨212353,21,(.group 5 3782 false)⟩)
(.leaf ⟨212374,21,(.group 5 3783 false)⟩))
(.branch 212416
(.leaf ⟨212395,21,(.group 5 3784 false)⟩)
(.leaf ⟨212416,21,(.group 5 3785 false)⟩)))
(.branch 212479
(.branch 212458
(.leaf ⟨212437,21,(.group 5 3786 false)⟩)
(.leaf ⟨212458,21,(.group 5 3787 false)⟩))
(.branch 212500
(.leaf ⟨212479,21,(.group 5 3788 false)⟩)
(.leaf ⟨212500,21,(.group 5 3789 false)⟩))))
(.branch 212605
(.branch 212563
(.branch 212542
(.leaf ⟨212521,21,(.group 5 3790 false)⟩)
(.leaf ⟨212542,21,(.group 5 3791 false)⟩))
(.branch 212584
(.leaf ⟨212563,21,(.group 5 3792 false)⟩)
(.leaf ⟨212584,21,(.group 5 3793 false)⟩)))
(.branch 212647
(.branch 212626
(.leaf ⟨212605,21,(.group 5 3794 false)⟩)
(.leaf ⟨212626,21,(.group 5 3795 false)⟩))
(.branch 212668
(.leaf ⟨212647,21,(.group 5 3796 false)⟩)
(.leaf ⟨212668,21,(.group 5 3797 false)⟩)))))
(.branch 212857
(.branch 212773
(.branch 212731
(.branch 212710
(.leaf ⟨212689,21,(.group 5 3798 false)⟩)
(.leaf ⟨212710,21,(.group 5 3799 false)⟩))
(.branch 212752
(.leaf ⟨212731,21,(.group 5 3800 false)⟩)
(.leaf ⟨212752,21,(.group 5 3801 false)⟩)))
(.branch 212815
(.branch 212794
(.leaf ⟨212773,21,(.group 5 3802 false)⟩)
(.leaf ⟨212794,21,(.group 5 3803 false)⟩))
(.branch 212836
(.leaf ⟨212815,21,(.group 5 3804 false)⟩)
(.leaf ⟨212836,21,(.group 5 3805 false)⟩))))
(.branch 212941
(.branch 212899
(.branch 212878
(.leaf ⟨212857,21,(.group 5 3806 false)⟩)
(.leaf ⟨212878,21,(.group 5 3807 false)⟩))
(.branch 212920
(.leaf ⟨212899,21,(.group 5 3808 false)⟩)
(.leaf ⟨212920,21,(.group 5 3809 false)⟩)))
(.branch 212983
(.branch 212962
(.leaf ⟨212941,21,(.group 5 3810 false)⟩)
(.leaf ⟨212962,21,(.group 5 3811 false)⟩))
(.branch 213004
(.leaf ⟨212983,21,(.group 5 3812 false)⟩)
(.leaf ⟨213004,21,(.group 5 3813 false)⟩))))))
(.branch 213361
(.branch 213193
(.branch 213109
(.branch 213067
(.branch 213046
(.leaf ⟨213025,21,(.group 5 3814 false)⟩)
(.leaf ⟨213046,21,(.group 5 3815 false)⟩))
(.branch 213088
(.leaf ⟨213067,21,(.group 5 3816 false)⟩)
(.leaf ⟨213088,21,(.group 5 3817 false)⟩)))
(.branch 213151
(.branch 213130
(.leaf ⟨213109,21,(.group 5 3818 false)⟩)
(.leaf ⟨213130,21,(.group 5 3819 false)⟩))
(.branch 213172
(.leaf ⟨213151,21,(.group 5 3820 false)⟩)
(.leaf ⟨213172,21,(.group 5 3821 false)⟩))))
(.branch 213277
(.branch 213235
(.branch 213214
(.leaf ⟨213193,21,(.group 5 3822 false)⟩)
(.leaf ⟨213214,21,(.group 5 3823 false)⟩))
(.branch 213256
(.leaf ⟨213235,21,(.group 5 3824 false)⟩)
(.leaf ⟨213256,21,(.group 5 3825 false)⟩)))
(.branch 213319
(.branch 213298
(.leaf ⟨213277,21,(.group 5 3826 false)⟩)
(.leaf ⟨213298,21,(.group 5 3827 false)⟩))
(.branch 213340
(.leaf ⟨213319,21,(.group 5 3828 false)⟩)
(.leaf ⟨213340,21,(.group 5 3829 false)⟩)))))
(.branch 213529
(.branch 213445
(.branch 213403
(.branch 213382
(.leaf ⟨213361,21,(.group 5 3830 false)⟩)
(.leaf ⟨213382,21,(.group 5 3831 false)⟩))
(.branch 213424
(.leaf ⟨213403,21,(.group 5 3832 false)⟩)
(.leaf ⟨213424,21,(.group 5 3833 false)⟩)))
(.branch 213487
(.branch 213466
(.leaf ⟨213445,21,(.group 5 3834 false)⟩)
(.leaf ⟨213466,21,(.group 5 3835 false)⟩))
(.branch 213508
(.leaf ⟨213487,21,(.group 5 3836 false)⟩)
(.leaf ⟨213508,21,(.group 5 3837 false)⟩))))
(.branch 213613
(.branch 213571
(.branch 213550
(.leaf ⟨213529,21,(.group 5 3838 false)⟩)
(.leaf ⟨213550,21,(.group 5 3839 false)⟩))
(.branch 213592
(.leaf ⟨213571,21,(.group 5 3840 false)⟩)
(.leaf ⟨213592,21,(.group 5 3841 false)⟩)))
(.branch 213655
(.branch 213634
(.leaf ⟨213613,21,(.group 5 3842 false)⟩)
(.leaf ⟨213634,21,(.group 5 3843 false)⟩))
(.branch 213676
(.leaf ⟨213655,21,(.group 5 3844 false)⟩)
(.leaf ⟨213676,21,(.group 5 3845 false)⟩)))))))

theorem tree199_checked : tree199.check 212353 213697 = true := by decide +kernel

def tree200 : Tree := (.branch 214369
(.branch 214033
(.branch 213865
(.branch 213781
(.branch 213739
(.branch 213718
(.leaf ⟨213697,21,(.group 5 3846 false)⟩)
(.leaf ⟨213718,21,(.group 5 3847 false)⟩))
(.branch 213760
(.leaf ⟨213739,21,(.group 5 3848 false)⟩)
(.leaf ⟨213760,21,(.group 5 3849 false)⟩)))
(.branch 213823
(.branch 213802
(.leaf ⟨213781,21,(.group 5 3850 false)⟩)
(.leaf ⟨213802,21,(.group 5 3851 false)⟩))
(.branch 213844
(.leaf ⟨213823,21,(.group 5 3852 false)⟩)
(.leaf ⟨213844,21,(.group 5 3853 false)⟩))))
(.branch 213949
(.branch 213907
(.branch 213886
(.leaf ⟨213865,21,(.group 5 3854 false)⟩)
(.leaf ⟨213886,21,(.group 5 3855 false)⟩))
(.branch 213928
(.leaf ⟨213907,21,(.group 5 3856 false)⟩)
(.leaf ⟨213928,21,(.group 5 3857 false)⟩)))
(.branch 213991
(.branch 213970
(.leaf ⟨213949,21,(.group 5 3858 false)⟩)
(.leaf ⟨213970,21,(.group 5 3859 false)⟩))
(.branch 214012
(.leaf ⟨213991,21,(.group 5 3860 false)⟩)
(.leaf ⟨214012,21,(.group 5 3861 false)⟩)))))
(.branch 214201
(.branch 214117
(.branch 214075
(.branch 214054
(.leaf ⟨214033,21,(.group 5 3862 false)⟩)
(.leaf ⟨214054,21,(.group 5 3863 false)⟩))
(.branch 214096
(.leaf ⟨214075,21,(.group 5 3864 false)⟩)
(.leaf ⟨214096,21,(.group 5 3865 false)⟩)))
(.branch 214159
(.branch 214138
(.leaf ⟨214117,21,(.group 5 3866 false)⟩)
(.leaf ⟨214138,21,(.group 5 3867 false)⟩))
(.branch 214180
(.leaf ⟨214159,21,(.group 5 3868 false)⟩)
(.leaf ⟨214180,21,(.group 5 3869 false)⟩))))
(.branch 214285
(.branch 214243
(.branch 214222
(.leaf ⟨214201,21,(.group 5 3870 false)⟩)
(.leaf ⟨214222,21,(.group 5 3871 false)⟩))
(.branch 214264
(.leaf ⟨214243,21,(.group 5 3872 false)⟩)
(.leaf ⟨214264,21,(.group 5 3873 false)⟩)))
(.branch 214327
(.branch 214306
(.leaf ⟨214285,21,(.group 5 3874 false)⟩)
(.leaf ⟨214306,21,(.group 5 3875 false)⟩))
(.branch 214348
(.leaf ⟨214327,21,(.group 5 3876 false)⟩)
(.leaf ⟨214348,21,(.group 5 3877 false)⟩))))))
(.branch 214705
(.branch 214537
(.branch 214453
(.branch 214411
(.branch 214390
(.leaf ⟨214369,21,(.group 5 3878 false)⟩)
(.leaf ⟨214390,21,(.group 5 3879 false)⟩))
(.branch 214432
(.leaf ⟨214411,21,(.group 5 3880 false)⟩)
(.leaf ⟨214432,21,(.group 5 3881 false)⟩)))
(.branch 214495
(.branch 214474
(.leaf ⟨214453,21,(.group 5 3882 false)⟩)
(.leaf ⟨214474,21,(.group 5 3883 false)⟩))
(.branch 214516
(.leaf ⟨214495,21,(.group 5 3884 false)⟩)
(.leaf ⟨214516,21,(.group 5 3885 false)⟩))))
(.branch 214621
(.branch 214579
(.branch 214558
(.leaf ⟨214537,21,(.group 5 3886 false)⟩)
(.leaf ⟨214558,21,(.group 5 3887 false)⟩))
(.branch 214600
(.leaf ⟨214579,21,(.group 5 3888 false)⟩)
(.leaf ⟨214600,21,(.group 5 3889 false)⟩)))
(.branch 214663
(.branch 214642
(.leaf ⟨214621,21,(.group 5 3890 false)⟩)
(.leaf ⟨214642,21,(.group 5 3891 false)⟩))
(.branch 214684
(.leaf ⟨214663,21,(.group 5 3892 false)⟩)
(.leaf ⟨214684,21,(.group 5 3893 false)⟩)))))
(.branch 214873
(.branch 214789
(.branch 214747
(.branch 214726
(.leaf ⟨214705,21,(.group 5 3894 false)⟩)
(.leaf ⟨214726,21,(.group 5 3895 false)⟩))
(.branch 214768
(.leaf ⟨214747,21,(.group 5 3896 false)⟩)
(.leaf ⟨214768,21,(.group 5 3897 false)⟩)))
(.branch 214831
(.branch 214810
(.leaf ⟨214789,21,(.group 5 3898 false)⟩)
(.leaf ⟨214810,21,(.group 5 3899 false)⟩))
(.branch 214852
(.leaf ⟨214831,21,(.group 5 3900 false)⟩)
(.leaf ⟨214852,21,(.group 5 3901 false)⟩))))
(.branch 214957
(.branch 214915
(.branch 214894
(.leaf ⟨214873,21,(.group 5 3902 false)⟩)
(.leaf ⟨214894,21,(.group 5 3903 false)⟩))
(.branch 214936
(.leaf ⟨214915,21,(.group 5 3904 false)⟩)
(.leaf ⟨214936,21,(.group 5 3905 false)⟩)))
(.branch 214999
(.branch 214978
(.leaf ⟨214957,21,(.group 5 3906 false)⟩)
(.leaf ⟨214978,21,(.group 5 3907 false)⟩))
(.branch 215020
(.leaf ⟨214999,21,(.group 5 3908 false)⟩)
(.leaf ⟨215020,21,(.group 5 3909 false)⟩)))))))

theorem tree200_checked : tree200.check 213697 215041 = true := by decide +kernel

def tree201 : Tree := (.branch 215713
(.branch 215377
(.branch 215209
(.branch 215125
(.branch 215083
(.branch 215062
(.leaf ⟨215041,21,(.group 5 3910 false)⟩)
(.leaf ⟨215062,21,(.group 5 3911 false)⟩))
(.branch 215104
(.leaf ⟨215083,21,(.group 5 3912 false)⟩)
(.leaf ⟨215104,21,(.group 5 3913 false)⟩)))
(.branch 215167
(.branch 215146
(.leaf ⟨215125,21,(.group 5 3914 false)⟩)
(.leaf ⟨215146,21,(.group 5 3915 false)⟩))
(.branch 215188
(.leaf ⟨215167,21,(.group 5 3916 false)⟩)
(.leaf ⟨215188,21,(.group 5 3917 false)⟩))))
(.branch 215293
(.branch 215251
(.branch 215230
(.leaf ⟨215209,21,(.group 5 3918 false)⟩)
(.leaf ⟨215230,21,(.group 5 3919 false)⟩))
(.branch 215272
(.leaf ⟨215251,21,(.group 5 3920 false)⟩)
(.leaf ⟨215272,21,(.group 5 3921 false)⟩)))
(.branch 215335
(.branch 215314
(.leaf ⟨215293,21,(.group 5 3922 false)⟩)
(.leaf ⟨215314,21,(.group 5 3923 false)⟩))
(.branch 215356
(.leaf ⟨215335,21,(.group 5 3924 false)⟩)
(.leaf ⟨215356,21,(.group 5 3925 false)⟩)))))
(.branch 215545
(.branch 215461
(.branch 215419
(.branch 215398
(.leaf ⟨215377,21,(.group 5 3926 false)⟩)
(.leaf ⟨215398,21,(.group 5 3927 false)⟩))
(.branch 215440
(.leaf ⟨215419,21,(.group 5 3928 false)⟩)
(.leaf ⟨215440,21,(.group 5 3929 false)⟩)))
(.branch 215503
(.branch 215482
(.leaf ⟨215461,21,(.group 5 3930 false)⟩)
(.leaf ⟨215482,21,(.group 5 3931 false)⟩))
(.branch 215524
(.leaf ⟨215503,21,(.group 5 3932 false)⟩)
(.leaf ⟨215524,21,(.group 5 3933 false)⟩))))
(.branch 215629
(.branch 215587
(.branch 215566
(.leaf ⟨215545,21,(.group 5 3934 false)⟩)
(.leaf ⟨215566,21,(.group 5 3935 false)⟩))
(.branch 215608
(.leaf ⟨215587,21,(.group 5 3936 false)⟩)
(.leaf ⟨215608,21,(.group 5 3937 false)⟩)))
(.branch 215671
(.branch 215650
(.leaf ⟨215629,21,(.group 5 3938 false)⟩)
(.leaf ⟨215650,21,(.group 5 3939 false)⟩))
(.branch 215692
(.leaf ⟨215671,21,(.group 5 3940 false)⟩)
(.leaf ⟨215692,21,(.group 5 3941 false)⟩))))))
(.branch 216049
(.branch 215881
(.branch 215797
(.branch 215755
(.branch 215734
(.leaf ⟨215713,21,(.group 5 3942 false)⟩)
(.leaf ⟨215734,21,(.group 5 3943 false)⟩))
(.branch 215776
(.leaf ⟨215755,21,(.group 5 3944 false)⟩)
(.leaf ⟨215776,21,(.group 5 3945 false)⟩)))
(.branch 215839
(.branch 215818
(.leaf ⟨215797,21,(.group 5 3946 false)⟩)
(.leaf ⟨215818,21,(.group 5 3947 false)⟩))
(.branch 215860
(.leaf ⟨215839,21,(.group 5 3948 false)⟩)
(.leaf ⟨215860,21,(.group 5 3949 false)⟩))))
(.branch 215965
(.branch 215923
(.branch 215902
(.leaf ⟨215881,21,(.group 5 3950 false)⟩)
(.leaf ⟨215902,21,(.group 5 3951 false)⟩))
(.branch 215944
(.leaf ⟨215923,21,(.group 5 3952 false)⟩)
(.leaf ⟨215944,21,(.group 5 3953 false)⟩)))
(.branch 216007
(.branch 215986
(.leaf ⟨215965,21,(.group 5 3954 false)⟩)
(.leaf ⟨215986,21,(.group 5 3955 false)⟩))
(.branch 216028
(.leaf ⟨216007,21,(.group 5 3956 false)⟩)
(.leaf ⟨216028,21,(.group 5 3957 false)⟩)))))
(.branch 216217
(.branch 216133
(.branch 216091
(.branch 216070
(.leaf ⟨216049,21,(.group 5 3958 false)⟩)
(.leaf ⟨216070,21,(.group 5 3959 false)⟩))
(.branch 216112
(.leaf ⟨216091,21,(.group 5 3960 false)⟩)
(.leaf ⟨216112,21,(.group 5 3961 false)⟩)))
(.branch 216175
(.branch 216154
(.leaf ⟨216133,21,(.group 5 3962 false)⟩)
(.leaf ⟨216154,21,(.group 5 3963 false)⟩))
(.branch 216196
(.leaf ⟨216175,21,(.group 5 3964 false)⟩)
(.leaf ⟨216196,21,(.group 5 3965 false)⟩))))
(.branch 216301
(.branch 216259
(.branch 216238
(.leaf ⟨216217,21,(.group 5 3966 false)⟩)
(.leaf ⟨216238,21,(.group 5 3967 false)⟩))
(.branch 216280
(.leaf ⟨216259,21,(.group 5 3968 false)⟩)
(.leaf ⟨216280,21,(.group 5 3969 false)⟩)))
(.branch 216343
(.branch 216322
(.leaf ⟨216301,21,(.group 5 3970 false)⟩)
(.leaf ⟨216322,21,(.group 5 3971 false)⟩))
(.branch 216364
(.leaf ⟨216343,21,(.group 5 3972 false)⟩)
(.leaf ⟨216364,21,(.group 5 3973 false)⟩)))))))

theorem tree201_checked : tree201.check 215041 216385 = true := by decide +kernel

def tree202 : Tree := (.branch 217057
(.branch 216721
(.branch 216553
(.branch 216469
(.branch 216427
(.branch 216406
(.leaf ⟨216385,21,(.group 5 3974 false)⟩)
(.leaf ⟨216406,21,(.group 5 3975 false)⟩))
(.branch 216448
(.leaf ⟨216427,21,(.group 5 3976 false)⟩)
(.leaf ⟨216448,21,(.group 5 3977 false)⟩)))
(.branch 216511
(.branch 216490
(.leaf ⟨216469,21,(.group 5 3978 false)⟩)
(.leaf ⟨216490,21,(.group 5 3979 false)⟩))
(.branch 216532
(.leaf ⟨216511,21,(.group 5 3980 false)⟩)
(.leaf ⟨216532,21,(.group 5 3981 false)⟩))))
(.branch 216637
(.branch 216595
(.branch 216574
(.leaf ⟨216553,21,(.group 5 3982 false)⟩)
(.leaf ⟨216574,21,(.group 5 3983 false)⟩))
(.branch 216616
(.leaf ⟨216595,21,(.group 5 3984 false)⟩)
(.leaf ⟨216616,21,(.group 5 3985 false)⟩)))
(.branch 216679
(.branch 216658
(.leaf ⟨216637,21,(.group 5 3986 false)⟩)
(.leaf ⟨216658,21,(.group 5 3987 false)⟩))
(.branch 216700
(.leaf ⟨216679,21,(.group 5 3988 false)⟩)
(.leaf ⟨216700,21,(.group 5 3989 false)⟩)))))
(.branch 216889
(.branch 216805
(.branch 216763
(.branch 216742
(.leaf ⟨216721,21,(.group 5 3990 false)⟩)
(.leaf ⟨216742,21,(.group 5 3991 false)⟩))
(.branch 216784
(.leaf ⟨216763,21,(.group 5 3992 false)⟩)
(.leaf ⟨216784,21,(.group 5 3993 false)⟩)))
(.branch 216847
(.branch 216826
(.leaf ⟨216805,21,(.group 5 3994 false)⟩)
(.leaf ⟨216826,21,(.group 5 3995 false)⟩))
(.branch 216868
(.leaf ⟨216847,21,(.group 5 3996 false)⟩)
(.leaf ⟨216868,21,(.group 5 3997 false)⟩))))
(.branch 216973
(.branch 216931
(.branch 216910
(.leaf ⟨216889,21,(.group 5 3998 false)⟩)
(.leaf ⟨216910,21,(.group 5 3999 false)⟩))
(.branch 216952
(.leaf ⟨216931,21,(.group 5 4000 false)⟩)
(.leaf ⟨216952,21,(.group 5 4001 false)⟩)))
(.branch 217015
(.branch 216994
(.leaf ⟨216973,21,(.group 5 4002 false)⟩)
(.leaf ⟨216994,21,(.group 5 4003 false)⟩))
(.branch 217036
(.leaf ⟨217015,21,(.group 5 4004 false)⟩)
(.leaf ⟨217036,21,(.group 5 4005 false)⟩))))))
(.branch 217393
(.branch 217225
(.branch 217141
(.branch 217099
(.branch 217078
(.leaf ⟨217057,21,(.group 5 4006 false)⟩)
(.leaf ⟨217078,21,(.group 5 4007 false)⟩))
(.branch 217120
(.leaf ⟨217099,21,(.group 5 4008 false)⟩)
(.leaf ⟨217120,21,(.group 5 4009 false)⟩)))
(.branch 217183
(.branch 217162
(.leaf ⟨217141,21,(.group 5 4010 false)⟩)
(.leaf ⟨217162,21,(.group 5 4011 false)⟩))
(.branch 217204
(.leaf ⟨217183,21,(.group 5 4012 false)⟩)
(.leaf ⟨217204,21,(.group 5 4013 false)⟩))))
(.branch 217309
(.branch 217267
(.branch 217246
(.leaf ⟨217225,21,(.group 5 4014 false)⟩)
(.leaf ⟨217246,21,(.group 5 4015 false)⟩))
(.branch 217288
(.leaf ⟨217267,21,(.group 5 4016 false)⟩)
(.leaf ⟨217288,21,(.group 5 4017 false)⟩)))
(.branch 217351
(.branch 217330
(.leaf ⟨217309,21,(.group 5 4018 false)⟩)
(.leaf ⟨217330,21,(.group 5 4019 false)⟩))
(.branch 217372
(.leaf ⟨217351,21,(.group 5 4020 false)⟩)
(.leaf ⟨217372,21,(.group 5 4021 false)⟩)))))
(.branch 217561
(.branch 217477
(.branch 217435
(.branch 217414
(.leaf ⟨217393,21,(.group 5 4022 false)⟩)
(.leaf ⟨217414,21,(.group 5 4023 false)⟩))
(.branch 217456
(.leaf ⟨217435,21,(.group 5 4024 false)⟩)
(.leaf ⟨217456,21,(.group 5 4025 false)⟩)))
(.branch 217519
(.branch 217498
(.leaf ⟨217477,21,(.group 5 4026 false)⟩)
(.leaf ⟨217498,21,(.group 5 4027 false)⟩))
(.branch 217540
(.leaf ⟨217519,21,(.group 5 4028 false)⟩)
(.leaf ⟨217540,21,(.group 5 4029 false)⟩))))
(.branch 217645
(.branch 217603
(.branch 217582
(.leaf ⟨217561,21,(.group 5 4030 false)⟩)
(.leaf ⟨217582,21,(.group 5 4031 false)⟩))
(.branch 217624
(.leaf ⟨217603,21,(.group 5 4032 false)⟩)
(.leaf ⟨217624,21,(.group 5 4033 false)⟩)))
(.branch 217687
(.branch 217666
(.leaf ⟨217645,21,(.group 5 4034 false)⟩)
(.leaf ⟨217666,21,(.group 5 4035 false)⟩))
(.branch 217708
(.leaf ⟨217687,21,(.group 5 4036 false)⟩)
(.leaf ⟨217708,21,(.group 5 4037 false)⟩)))))))

theorem tree202_checked : tree202.check 216385 217729 = true := by decide +kernel

def tree203 : Tree := (.branch 218401
(.branch 218065
(.branch 217897
(.branch 217813
(.branch 217771
(.branch 217750
(.leaf ⟨217729,21,(.group 5 4038 false)⟩)
(.leaf ⟨217750,21,(.group 5 4039 false)⟩))
(.branch 217792
(.leaf ⟨217771,21,(.group 5 4040 false)⟩)
(.leaf ⟨217792,21,(.group 5 4041 false)⟩)))
(.branch 217855
(.branch 217834
(.leaf ⟨217813,21,(.group 5 4042 false)⟩)
(.leaf ⟨217834,21,(.group 5 4043 false)⟩))
(.branch 217876
(.leaf ⟨217855,21,(.group 5 4044 false)⟩)
(.leaf ⟨217876,21,(.group 5 4045 false)⟩))))
(.branch 217981
(.branch 217939
(.branch 217918
(.leaf ⟨217897,21,(.group 5 4046 false)⟩)
(.leaf ⟨217918,21,(.group 5 4047 false)⟩))
(.branch 217960
(.leaf ⟨217939,21,(.group 5 4048 false)⟩)
(.leaf ⟨217960,21,(.group 5 4049 false)⟩)))
(.branch 218023
(.branch 218002
(.leaf ⟨217981,21,(.group 5 4050 false)⟩)
(.leaf ⟨218002,21,(.group 5 4051 false)⟩))
(.branch 218044
(.leaf ⟨218023,21,(.group 5 4052 false)⟩)
(.leaf ⟨218044,21,(.group 5 4053 false)⟩)))))
(.branch 218233
(.branch 218149
(.branch 218107
(.branch 218086
(.leaf ⟨218065,21,(.group 5 4054 false)⟩)
(.leaf ⟨218086,21,(.group 5 4055 false)⟩))
(.branch 218128
(.leaf ⟨218107,21,(.group 5 4056 false)⟩)
(.leaf ⟨218128,21,(.group 5 4057 false)⟩)))
(.branch 218191
(.branch 218170
(.leaf ⟨218149,21,(.group 5 4058 false)⟩)
(.leaf ⟨218170,21,(.group 5 4059 false)⟩))
(.branch 218212
(.leaf ⟨218191,21,(.group 5 4060 false)⟩)
(.leaf ⟨218212,21,(.group 5 4061 false)⟩))))
(.branch 218317
(.branch 218275
(.branch 218254
(.leaf ⟨218233,21,(.group 5 4062 false)⟩)
(.leaf ⟨218254,21,(.group 5 4063 false)⟩))
(.branch 218296
(.leaf ⟨218275,21,(.group 5 4064 false)⟩)
(.leaf ⟨218296,21,(.group 5 4065 false)⟩)))
(.branch 218359
(.branch 218338
(.leaf ⟨218317,21,(.group 5 4066 false)⟩)
(.leaf ⟨218338,21,(.group 5 4067 false)⟩))
(.branch 218380
(.leaf ⟨218359,21,(.group 5 4068 false)⟩)
(.leaf ⟨218380,21,(.group 5 4069 false)⟩))))))
(.branch 218737
(.branch 218569
(.branch 218485
(.branch 218443
(.branch 218422
(.leaf ⟨218401,21,(.group 5 4070 false)⟩)
(.leaf ⟨218422,21,(.group 5 4071 false)⟩))
(.branch 218464
(.leaf ⟨218443,21,(.group 5 4072 false)⟩)
(.leaf ⟨218464,21,(.group 5 4073 false)⟩)))
(.branch 218527
(.branch 218506
(.leaf ⟨218485,21,(.group 5 4074 false)⟩)
(.leaf ⟨218506,21,(.group 5 4075 false)⟩))
(.branch 218548
(.leaf ⟨218527,21,(.group 5 4076 false)⟩)
(.leaf ⟨218548,21,(.group 5 4077 false)⟩))))
(.branch 218653
(.branch 218611
(.branch 218590
(.leaf ⟨218569,21,(.group 5 4078 false)⟩)
(.leaf ⟨218590,21,(.group 5 4079 false)⟩))
(.branch 218632
(.leaf ⟨218611,21,(.group 5 4080 false)⟩)
(.leaf ⟨218632,21,(.group 5 4081 false)⟩)))
(.branch 218695
(.branch 218674
(.leaf ⟨218653,21,(.group 5 4082 false)⟩)
(.leaf ⟨218674,21,(.group 5 4083 false)⟩))
(.branch 218716
(.leaf ⟨218695,21,(.group 5 4084 false)⟩)
(.leaf ⟨218716,21,(.group 5 4085 false)⟩)))))
(.branch 218905
(.branch 218821
(.branch 218779
(.branch 218758
(.leaf ⟨218737,21,(.group 5 4086 false)⟩)
(.leaf ⟨218758,21,(.group 5 4087 false)⟩))
(.branch 218800
(.leaf ⟨218779,21,(.group 5 4088 false)⟩)
(.leaf ⟨218800,21,(.group 5 4089 false)⟩)))
(.branch 218863
(.branch 218842
(.leaf ⟨218821,21,(.group 5 4090 false)⟩)
(.leaf ⟨218842,21,(.group 5 4091 false)⟩))
(.branch 218884
(.leaf ⟨218863,21,(.group 5 4092 false)⟩)
(.leaf ⟨218884,21,(.group 5 4093 false)⟩))))
(.branch 218989
(.branch 218947
(.branch 218926
(.leaf ⟨218905,21,(.group 5 4094 false)⟩)
(.leaf ⟨218926,21,(.group 5 4095 false)⟩))
(.branch 218968
(.leaf ⟨218947,21,(.group 7 593 false)⟩)
(.leaf ⟨218968,21,(.group 7 594 false)⟩)))
(.branch 219031
(.branch 219010
(.leaf ⟨218989,21,(.group 7 595 false)⟩)
(.leaf ⟨219010,21,(.group 7 596 false)⟩))
(.branch 219052
(.leaf ⟨219031,21,(.group 7 597 false)⟩)
(.leaf ⟨219052,21,(.group 7 598 false)⟩)))))))

theorem tree203_checked : tree203.check 217729 219073 = true := by decide +kernel

def tree204 : Tree := (.branch 219745
(.branch 219409
(.branch 219241
(.branch 219157
(.branch 219115
(.branch 219094
(.leaf ⟨219073,21,(.group 7 599 false)⟩)
(.leaf ⟨219094,21,(.group 7 600 false)⟩))
(.branch 219136
(.leaf ⟨219115,21,(.group 7 601 false)⟩)
(.leaf ⟨219136,21,(.group 7 602 false)⟩)))
(.branch 219199
(.branch 219178
(.leaf ⟨219157,21,(.group 7 603 false)⟩)
(.leaf ⟨219178,21,(.group 7 604 false)⟩))
(.branch 219220
(.leaf ⟨219199,21,(.group 7 605 false)⟩)
(.leaf ⟨219220,21,(.group 7 606 false)⟩))))
(.branch 219325
(.branch 219283
(.branch 219262
(.leaf ⟨219241,21,(.group 7 607 false)⟩)
(.leaf ⟨219262,21,(.group 7 608 false)⟩))
(.branch 219304
(.leaf ⟨219283,21,(.group 7 609 false)⟩)
(.leaf ⟨219304,21,(.group 7 610 false)⟩)))
(.branch 219367
(.branch 219346
(.leaf ⟨219325,21,(.group 7 611 false)⟩)
(.leaf ⟨219346,21,(.group 7 612 false)⟩))
(.branch 219388
(.leaf ⟨219367,21,(.group 7 613 false)⟩)
(.leaf ⟨219388,21,(.group 7 614 false)⟩)))))
(.branch 219577
(.branch 219493
(.branch 219451
(.branch 219430
(.leaf ⟨219409,21,(.group 7 615 false)⟩)
(.leaf ⟨219430,21,(.group 7 616 false)⟩))
(.branch 219472
(.leaf ⟨219451,21,(.group 7 617 false)⟩)
(.leaf ⟨219472,21,(.group 7 618 false)⟩)))
(.branch 219535
(.branch 219514
(.leaf ⟨219493,21,(.group 7 619 false)⟩)
(.leaf ⟨219514,21,(.group 7 620 false)⟩))
(.branch 219556
(.leaf ⟨219535,21,(.group 7 621 false)⟩)
(.leaf ⟨219556,21,(.group 7 622 false)⟩))))
(.branch 219661
(.branch 219619
(.branch 219598
(.leaf ⟨219577,21,(.group 7 623 false)⟩)
(.leaf ⟨219598,21,(.group 7 624 false)⟩))
(.branch 219640
(.leaf ⟨219619,21,(.group 7 625 false)⟩)
(.leaf ⟨219640,21,(.group 7 626 false)⟩)))
(.branch 219703
(.branch 219682
(.leaf ⟨219661,21,(.group 7 627 false)⟩)
(.leaf ⟨219682,21,(.group 7 628 false)⟩))
(.branch 219724
(.leaf ⟨219703,21,(.group 7 629 false)⟩)
(.leaf ⟨219724,21,(.group 7 630 false)⟩))))))
(.branch 220081
(.branch 219913
(.branch 219829
(.branch 219787
(.branch 219766
(.leaf ⟨219745,21,(.group 7 631 false)⟩)
(.leaf ⟨219766,21,(.group 7 632 false)⟩))
(.branch 219808
(.leaf ⟨219787,21,(.group 7 633 false)⟩)
(.leaf ⟨219808,21,(.group 7 634 false)⟩)))
(.branch 219871
(.branch 219850
(.leaf ⟨219829,21,(.group 7 635 false)⟩)
(.leaf ⟨219850,21,(.group 7 636 false)⟩))
(.branch 219892
(.leaf ⟨219871,21,(.group 7 637 false)⟩)
(.leaf ⟨219892,21,(.group 7 638 false)⟩))))
(.branch 219997
(.branch 219955
(.branch 219934
(.leaf ⟨219913,21,(.group 7 639 false)⟩)
(.leaf ⟨219934,21,(.group 7 640 false)⟩))
(.branch 219976
(.leaf ⟨219955,21,(.group 7 641 false)⟩)
(.leaf ⟨219976,21,(.group 7 642 false)⟩)))
(.branch 220039
(.branch 220018
(.leaf ⟨219997,21,(.group 7 643 false)⟩)
(.leaf ⟨220018,21,(.group 7 644 false)⟩))
(.branch 220060
(.leaf ⟨220039,21,(.group 7 645 false)⟩)
(.leaf ⟨220060,21,(.group 7 646 false)⟩)))))
(.branch 220249
(.branch 220165
(.branch 220123
(.branch 220102
(.leaf ⟨220081,21,(.group 7 647 false)⟩)
(.leaf ⟨220102,21,(.group 7 648 false)⟩))
(.branch 220144
(.leaf ⟨220123,21,(.group 7 649 false)⟩)
(.leaf ⟨220144,21,(.group 7 650 false)⟩)))
(.branch 220207
(.branch 220186
(.leaf ⟨220165,21,(.group 7 651 false)⟩)
(.leaf ⟨220186,21,(.group 7 652 false)⟩))
(.branch 220228
(.leaf ⟨220207,21,(.group 7 653 false)⟩)
(.leaf ⟨220228,21,(.group 7 654 false)⟩))))
(.branch 220333
(.branch 220291
(.branch 220270
(.leaf ⟨220249,21,(.group 7 655 false)⟩)
(.leaf ⟨220270,21,(.group 7 656 false)⟩))
(.branch 220312
(.leaf ⟨220291,21,(.group 7 657 false)⟩)
(.leaf ⟨220312,21,(.group 7 658 false)⟩)))
(.branch 220375
(.branch 220354
(.leaf ⟨220333,21,(.group 7 659 false)⟩)
(.leaf ⟨220354,21,(.group 7 660 false)⟩))
(.branch 220396
(.leaf ⟨220375,21,(.group 7 661 false)⟩)
(.leaf ⟨220396,21,(.group 7 662 false)⟩)))))))

theorem tree204_checked : tree204.check 219073 220417 = true := by decide +kernel

def tree205 : Tree := (.branch 221089
(.branch 220753
(.branch 220585
(.branch 220501
(.branch 220459
(.branch 220438
(.leaf ⟨220417,21,(.group 7 663 false)⟩)
(.leaf ⟨220438,21,(.group 7 664 false)⟩))
(.branch 220480
(.leaf ⟨220459,21,(.group 7 665 false)⟩)
(.leaf ⟨220480,21,(.group 7 666 false)⟩)))
(.branch 220543
(.branch 220522
(.leaf ⟨220501,21,(.group 7 667 false)⟩)
(.leaf ⟨220522,21,(.group 7 668 false)⟩))
(.branch 220564
(.leaf ⟨220543,21,(.group 7 669 false)⟩)
(.leaf ⟨220564,21,(.group 7 670 false)⟩))))
(.branch 220669
(.branch 220627
(.branch 220606
(.leaf ⟨220585,21,(.group 7 671 false)⟩)
(.leaf ⟨220606,21,(.group 7 672 false)⟩))
(.branch 220648
(.leaf ⟨220627,21,(.group 7 673 false)⟩)
(.leaf ⟨220648,21,(.group 7 674 false)⟩)))
(.branch 220711
(.branch 220690
(.leaf ⟨220669,21,(.group 7 675 false)⟩)
(.leaf ⟨220690,21,(.group 7 676 false)⟩))
(.branch 220732
(.leaf ⟨220711,21,(.group 7 677 false)⟩)
(.leaf ⟨220732,21,(.group 7 678 false)⟩)))))
(.branch 220921
(.branch 220837
(.branch 220795
(.branch 220774
(.leaf ⟨220753,21,(.group 7 679 false)⟩)
(.leaf ⟨220774,21,(.group 7 680 false)⟩))
(.branch 220816
(.leaf ⟨220795,21,(.group 7 681 false)⟩)
(.leaf ⟨220816,21,(.group 7 682 false)⟩)))
(.branch 220879
(.branch 220858
(.leaf ⟨220837,21,(.group 7 683 false)⟩)
(.leaf ⟨220858,21,(.group 7 684 false)⟩))
(.branch 220900
(.leaf ⟨220879,21,(.group 7 685 false)⟩)
(.leaf ⟨220900,21,(.group 7 686 false)⟩))))
(.branch 221005
(.branch 220963
(.branch 220942
(.leaf ⟨220921,21,(.group 7 687 false)⟩)
(.leaf ⟨220942,21,(.group 7 688 false)⟩))
(.branch 220984
(.leaf ⟨220963,21,(.group 7 689 false)⟩)
(.leaf ⟨220984,21,(.group 7 690 false)⟩)))
(.branch 221047
(.branch 221026
(.leaf ⟨221005,21,(.group 7 691 false)⟩)
(.leaf ⟨221026,21,(.group 7 692 false)⟩))
(.branch 221068
(.leaf ⟨221047,21,(.group 7 693 false)⟩)
(.leaf ⟨221068,21,(.group 7 694 false)⟩))))))
(.branch 221425
(.branch 221257
(.branch 221173
(.branch 221131
(.branch 221110
(.leaf ⟨221089,21,(.group 7 695 false)⟩)
(.leaf ⟨221110,21,(.group 7 696 false)⟩))
(.branch 221152
(.leaf ⟨221131,21,(.group 7 697 false)⟩)
(.leaf ⟨221152,21,(.group 7 698 false)⟩)))
(.branch 221215
(.branch 221194
(.leaf ⟨221173,21,(.group 7 699 false)⟩)
(.leaf ⟨221194,21,(.group 7 700 false)⟩))
(.branch 221236
(.leaf ⟨221215,21,(.group 7 701 false)⟩)
(.leaf ⟨221236,21,(.group 7 702 false)⟩))))
(.branch 221341
(.branch 221299
(.branch 221278
(.leaf ⟨221257,21,(.group 7 703 false)⟩)
(.leaf ⟨221278,21,(.group 7 704 false)⟩))
(.branch 221320
(.leaf ⟨221299,21,(.group 7 705 false)⟩)
(.leaf ⟨221320,21,(.group 7 706 false)⟩)))
(.branch 221383
(.branch 221362
(.leaf ⟨221341,21,(.group 7 707 false)⟩)
(.leaf ⟨221362,21,(.group 7 708 false)⟩))
(.branch 221404
(.leaf ⟨221383,21,(.group 7 709 false)⟩)
(.leaf ⟨221404,21,(.group 7 710 false)⟩)))))
(.branch 221593
(.branch 221509
(.branch 221467
(.branch 221446
(.leaf ⟨221425,21,(.group 7 711 false)⟩)
(.leaf ⟨221446,21,(.group 7 712 false)⟩))
(.branch 221488
(.leaf ⟨221467,21,(.group 8 720 false)⟩)
(.leaf ⟨221488,21,(.group 8 721 false)⟩)))
(.branch 221551
(.branch 221530
(.leaf ⟨221509,21,(.group 8 722 false)⟩)
(.leaf ⟨221530,21,(.group 8 723 false)⟩))
(.branch 221572
(.leaf ⟨221551,21,(.group 8 724 false)⟩)
(.leaf ⟨221572,21,(.group 8 725 false)⟩))))
(.branch 221677
(.branch 221635
(.branch 221614
(.leaf ⟨221593,21,(.group 8 726 false)⟩)
(.leaf ⟨221614,21,(.group 8 727 false)⟩))
(.branch 221656
(.leaf ⟨221635,21,(.group 8 728 false)⟩)
(.leaf ⟨221656,21,(.group 8 729 false)⟩)))
(.branch 221719
(.branch 221698
(.leaf ⟨221677,21,(.group 8 730 false)⟩)
(.leaf ⟨221698,21,(.group 8 731 false)⟩))
(.branch 221740
(.leaf ⟨221719,21,(.group 8 732 false)⟩)
(.leaf ⟨221740,22,(.group 7 713 false)⟩)))))))

theorem tree205_checked : tree205.check 220417 221762 = true := by decide +kernel

def tree206 : Tree := (.branch 222466
(.branch 222114
(.branch 221938
(.branch 221850
(.branch 221806
(.branch 221784
(.leaf ⟨221762,22,(.group 7 714 false)⟩)
(.leaf ⟨221784,22,(.group 7 715 false)⟩))
(.branch 221828
(.leaf ⟨221806,22,(.group 7 716 false)⟩)
(.leaf ⟨221828,22,(.group 7 717 false)⟩)))
(.branch 221894
(.branch 221872
(.leaf ⟨221850,22,(.group 7 718 false)⟩)
(.leaf ⟨221872,22,(.group 7 719 false)⟩))
(.branch 221916
(.leaf ⟨221894,22,(.group 7 720 false)⟩)
(.leaf ⟨221916,22,(.group 7 721 false)⟩))))
(.branch 222026
(.branch 221982
(.branch 221960
(.leaf ⟨221938,22,(.group 7 722 false)⟩)
(.leaf ⟨221960,22,(.group 7 723 false)⟩))
(.branch 222004
(.leaf ⟨221982,22,(.group 7 724 false)⟩)
(.leaf ⟨222004,22,(.group 7 725 false)⟩)))
(.branch 222070
(.branch 222048
(.leaf ⟨222026,22,(.group 7 726 false)⟩)
(.leaf ⟨222048,22,(.group 7 727 false)⟩))
(.branch 222092
(.leaf ⟨222070,22,(.group 7 728 false)⟩)
(.leaf ⟨222092,22,(.group 7 729 false)⟩)))))
(.branch 222290
(.branch 222202
(.branch 222158
(.branch 222136
(.leaf ⟨222114,22,(.group 7 730 false)⟩)
(.leaf ⟨222136,22,(.group 7 731 false)⟩))
(.branch 222180
(.leaf ⟨222158,22,(.group 7 732 false)⟩)
(.leaf ⟨222180,22,(.group 7 733 false)⟩)))
(.branch 222246
(.branch 222224
(.leaf ⟨222202,22,(.group 7 734 false)⟩)
(.leaf ⟨222224,22,(.group 7 735 false)⟩))
(.branch 222268
(.leaf ⟨222246,22,(.group 7 736 false)⟩)
(.leaf ⟨222268,22,(.group 7 737 false)⟩))))
(.branch 222378
(.branch 222334
(.branch 222312
(.leaf ⟨222290,22,(.group 7 738 false)⟩)
(.leaf ⟨222312,22,(.group 7 739 false)⟩))
(.branch 222356
(.leaf ⟨222334,22,(.group 7 740 false)⟩)
(.leaf ⟨222356,22,(.group 7 741 false)⟩)))
(.branch 222422
(.branch 222400
(.leaf ⟨222378,22,(.group 7 742 false)⟩)
(.leaf ⟨222400,22,(.group 7 743 false)⟩))
(.branch 222444
(.leaf ⟨222422,22,(.group 7 744 false)⟩)
(.leaf ⟨222444,22,(.group 7 745 false)⟩))))))
(.branch 222818
(.branch 222642
(.branch 222554
(.branch 222510
(.branch 222488
(.leaf ⟨222466,22,(.group 7 746 false)⟩)
(.leaf ⟨222488,22,(.group 7 747 false)⟩))
(.branch 222532
(.leaf ⟨222510,22,(.group 7 748 false)⟩)
(.leaf ⟨222532,22,(.group 7 749 false)⟩)))
(.branch 222598
(.branch 222576
(.leaf ⟨222554,22,(.group 7 750 false)⟩)
(.leaf ⟨222576,22,(.group 7 751 false)⟩))
(.branch 222620
(.leaf ⟨222598,22,(.group 7 752 false)⟩)
(.leaf ⟨222620,22,(.group 7 753 false)⟩))))
(.branch 222730
(.branch 222686
(.branch 222664
(.leaf ⟨222642,22,(.group 7 754 false)⟩)
(.leaf ⟨222664,22,(.group 7 755 false)⟩))
(.branch 222708
(.leaf ⟨222686,22,(.group 7 756 false)⟩)
(.leaf ⟨222708,22,(.group 7 757 false)⟩)))
(.branch 222774
(.branch 222752
(.leaf ⟨222730,22,(.group 7 758 false)⟩)
(.leaf ⟨222752,22,(.group 7 759 false)⟩))
(.branch 222796
(.leaf ⟨222774,22,(.group 7 760 false)⟩)
(.leaf ⟨222796,22,(.group 7 761 false)⟩)))))
(.branch 222994
(.branch 222906
(.branch 222862
(.branch 222840
(.leaf ⟨222818,22,(.group 7 762 false)⟩)
(.leaf ⟨222840,22,(.group 7 763 false)⟩))
(.branch 222884
(.leaf ⟨222862,22,(.group 7 764 false)⟩)
(.leaf ⟨222884,22,(.group 7 765 false)⟩)))
(.branch 222950
(.branch 222928
(.leaf ⟨222906,22,(.group 7 766 false)⟩)
(.leaf ⟨222928,22,(.group 7 767 false)⟩))
(.branch 222972
(.leaf ⟨222950,22,(.group 7 768 false)⟩)
(.leaf ⟨222972,22,(.group 7 769 false)⟩))))
(.branch 223082
(.branch 223038
(.branch 223016
(.leaf ⟨222994,22,(.group 7 770 false)⟩)
(.leaf ⟨223016,22,(.group 7 771 false)⟩))
(.branch 223060
(.leaf ⟨223038,22,(.group 7 772 false)⟩)
(.leaf ⟨223060,22,(.group 7 773 false)⟩)))
(.branch 223126
(.branch 223104
(.leaf ⟨223082,22,(.group 7 774 false)⟩)
(.leaf ⟨223104,22,(.group 7 775 false)⟩))
(.branch 223148
(.leaf ⟨223126,22,(.group 7 776 false)⟩)
(.leaf ⟨223148,22,(.group 7 777 false)⟩)))))))

theorem tree206_checked : tree206.check 221762 223170 = true := by decide +kernel

def tree207 : Tree := (.branch 223874
(.branch 223522
(.branch 223346
(.branch 223258
(.branch 223214
(.branch 223192
(.leaf ⟨223170,22,(.group 7 778 false)⟩)
(.leaf ⟨223192,22,(.group 7 779 false)⟩))
(.branch 223236
(.leaf ⟨223214,22,(.group 7 780 false)⟩)
(.leaf ⟨223236,22,(.group 7 781 false)⟩)))
(.branch 223302
(.branch 223280
(.leaf ⟨223258,22,(.group 7 782 false)⟩)
(.leaf ⟨223280,22,(.group 7 783 false)⟩))
(.branch 223324
(.leaf ⟨223302,22,(.group 7 784 false)⟩)
(.leaf ⟨223324,22,(.group 7 785 false)⟩))))
(.branch 223434
(.branch 223390
(.branch 223368
(.leaf ⟨223346,22,(.group 7 786 false)⟩)
(.leaf ⟨223368,22,(.group 7 787 false)⟩))
(.branch 223412
(.leaf ⟨223390,22,(.group 7 788 false)⟩)
(.leaf ⟨223412,22,(.group 7 789 false)⟩)))
(.branch 223478
(.branch 223456
(.leaf ⟨223434,22,(.group 7 790 false)⟩)
(.leaf ⟨223456,22,(.group 7 791 false)⟩))
(.branch 223500
(.leaf ⟨223478,22,(.group 7 792 false)⟩)
(.leaf ⟨223500,22,(.group 7 793 false)⟩)))))
(.branch 223698
(.branch 223610
(.branch 223566
(.branch 223544
(.leaf ⟨223522,22,(.group 7 794 false)⟩)
(.leaf ⟨223544,22,(.group 7 795 false)⟩))
(.branch 223588
(.leaf ⟨223566,22,(.group 7 796 false)⟩)
(.leaf ⟨223588,22,(.group 7 797 false)⟩)))
(.branch 223654
(.branch 223632
(.leaf ⟨223610,22,(.group 7 798 false)⟩)
(.leaf ⟨223632,22,(.group 7 799 false)⟩))
(.branch 223676
(.leaf ⟨223654,22,(.group 7 800 false)⟩)
(.leaf ⟨223676,22,(.group 7 801 false)⟩))))
(.branch 223786
(.branch 223742
(.branch 223720
(.leaf ⟨223698,22,(.group 7 802 false)⟩)
(.leaf ⟨223720,22,(.group 7 803 false)⟩))
(.branch 223764
(.leaf ⟨223742,22,(.group 7 804 false)⟩)
(.leaf ⟨223764,22,(.group 7 805 false)⟩)))
(.branch 223830
(.branch 223808
(.leaf ⟨223786,22,(.group 7 806 false)⟩)
(.leaf ⟨223808,22,(.group 7 807 false)⟩))
(.branch 223852
(.leaf ⟨223830,22,(.group 7 808 false)⟩)
(.leaf ⟨223852,22,(.group 7 809 false)⟩))))))
(.branch 224090
(.branch 224010
(.branch 223962
(.branch 223918
(.branch 223896
(.leaf ⟨223874,22,(.group 7 810 false)⟩)
(.leaf ⟨223896,22,(.group 7 811 false)⟩))
(.branch 223940
(.leaf ⟨223918,22,(.group 7 812 false)⟩)
(.leaf ⟨223940,22,(.group 7 813 false)⟩)))
(.branch 223992
(.branch 223984
(.leaf ⟨223962,22,(.group 7 814 false)⟩)
(.leaf ⟨223984,8,(.group 1 0 true)⟩))
(.branch 224001
(.leaf ⟨223992,9,(.group 1 1 true)⟩)
(.leaf ⟨224001,9,(.group 1 2 true)⟩))))
(.branch 224049
(.branch 224029
(.branch 224019
(.leaf ⟨224010,9,(.group 1 3 true)⟩)
(.leaf ⟨224019,10,(.group 1 4 true)⟩))
(.branch 224039
(.leaf ⟨224029,10,(.group 1 5 true)⟩)
(.leaf ⟨224039,10,(.group 1 6 true)⟩)))
(.branch 224069
(.branch 224059
(.leaf ⟨224049,10,(.group 1 7 true)⟩)
(.leaf ⟨224059,10,(.group 1 8 true)⟩))
(.branch 224079
(.leaf ⟨224069,10,(.group 1 9 true)⟩)
(.leaf ⟨224079,11,(.group 1 10 true)⟩)))))
(.branch 224178
(.branch 224134
(.branch 224112
(.branch 224101
(.leaf ⟨224090,11,(.group 1 11 true)⟩)
(.leaf ⟨224101,11,(.group 1 12 true)⟩))
(.branch 224123
(.leaf ⟨224112,11,(.group 1 13 true)⟩)
(.leaf ⟨224123,11,(.group 1 14 true)⟩)))
(.branch 224156
(.branch 224145
(.leaf ⟨224134,11,(.group 1 15 true)⟩)
(.leaf ⟨224145,11,(.group 1 16 true)⟩))
(.branch 224167
(.leaf ⟨224156,11,(.group 1 17 true)⟩)
(.leaf ⟨224167,11,(.group 1 18 true)⟩))))
(.branch 224225
(.branch 224201
(.branch 224189
(.leaf ⟨224178,11,(.group 1 19 true)⟩)
(.leaf ⟨224189,12,(.group 1 20 true)⟩))
(.branch 224213
(.leaf ⟨224201,12,(.group 1 21 true)⟩)
(.leaf ⟨224213,12,(.group 1 22 true)⟩)))
(.branch 224249
(.branch 224237
(.leaf ⟨224225,12,(.group 1 23 true)⟩)
(.leaf ⟨224237,12,(.group 1 24 true)⟩))
(.branch 224261
(.leaf ⟨224249,12,(.group 1 25 true)⟩)
(.leaf ⟨224261,12,(.group 1 26 true)⟩)))))))

theorem tree207_checked : tree207.check 223170 224273 = true := by decide +kernel

def tree208 : Tree := (.branch 224684
(.branch 224473
(.branch 224369
(.branch 224321
(.branch 224297
(.branch 224285
(.leaf ⟨224273,12,(.group 1 27 true)⟩)
(.leaf ⟨224285,12,(.group 1 28 true)⟩))
(.branch 224309
(.leaf ⟨224297,12,(.group 1 29 true)⟩)
(.leaf ⟨224309,12,(.group 1 30 true)⟩)))
(.branch 224345
(.branch 224333
(.leaf ⟨224321,12,(.group 1 31 true)⟩)
(.leaf ⟨224333,12,(.group 1 32 true)⟩))
(.branch 224357
(.leaf ⟨224345,12,(.group 1 33 true)⟩)
(.leaf ⟨224357,12,(.group 1 34 true)⟩))))
(.branch 224421
(.branch 224395
(.branch 224382
(.leaf ⟨224369,13,(.group 1 35 true)⟩)
(.leaf ⟨224382,13,(.group 1 36 true)⟩))
(.branch 224408
(.leaf ⟨224395,13,(.group 1 37 true)⟩)
(.leaf ⟨224408,13,(.group 1 38 true)⟩)))
(.branch 224447
(.branch 224434
(.leaf ⟨224421,13,(.group 1 39 true)⟩)
(.leaf ⟨224434,13,(.group 1 40 true)⟩))
(.branch 224460
(.leaf ⟨224447,13,(.group 1 41 true)⟩)
(.leaf ⟨224460,13,(.group 1 42 true)⟩)))))
(.branch 224577
(.branch 224525
(.branch 224499
(.branch 224486
(.leaf ⟨224473,13,(.group 1 43 true)⟩)
(.leaf ⟨224486,13,(.group 1 44 true)⟩))
(.branch 224512
(.leaf ⟨224499,13,(.group 1 45 true)⟩)
(.leaf ⟨224512,13,(.group 1 46 true)⟩)))
(.branch 224551
(.branch 224538
(.leaf ⟨224525,13,(.group 1 47 true)⟩)
(.leaf ⟨224538,13,(.group 1 48 true)⟩))
(.branch 224564
(.leaf ⟨224551,13,(.group 1 49 true)⟩)
(.leaf ⟨224564,13,(.group 1 50 true)⟩))))
(.branch 224629
(.branch 224603
(.branch 224590
(.leaf ⟨224577,13,(.group 1 51 true)⟩)
(.leaf ⟨224590,13,(.group 1 52 true)⟩))
(.branch 224616
(.leaf ⟨224603,13,(.group 1 53 true)⟩)
(.leaf ⟨224616,13,(.group 1 54 true)⟩)))
(.branch 224656
(.branch 224642
(.leaf ⟨224629,13,(.group 1 55 true)⟩)
(.leaf ⟨224642,14,(.group 1 56 true)⟩))
(.branch 224670
(.leaf ⟨224656,14,(.group 1 57 true)⟩)
(.leaf ⟨224670,14,(.group 1 58 true)⟩))))))
(.branch 224908
(.branch 224796
(.branch 224740
(.branch 224712
(.branch 224698
(.leaf ⟨224684,14,(.group 1 59 true)⟩)
(.leaf ⟨224698,14,(.group 1 60 true)⟩))
(.branch 224726
(.leaf ⟨224712,14,(.group 1 61 true)⟩)
(.leaf ⟨224726,14,(.group 1 62 true)⟩)))
(.branch 224768
(.branch 224754
(.leaf ⟨224740,14,(.group 1 63 true)⟩)
(.leaf ⟨224754,14,(.group 1 64 true)⟩))
(.branch 224782
(.leaf ⟨224768,14,(.group 1 65 true)⟩)
(.leaf ⟨224782,14,(.group 1 66 true)⟩))))
(.branch 224852
(.branch 224824
(.branch 224810
(.leaf ⟨224796,14,(.group 1 67 true)⟩)
(.leaf ⟨224810,14,(.group 1 68 true)⟩))
(.branch 224838
(.leaf ⟨224824,14,(.group 1 69 true)⟩)
(.leaf ⟨224838,14,(.group 1 70 true)⟩)))
(.branch 224880
(.branch 224866
(.leaf ⟨224852,14,(.group 1 71 true)⟩)
(.leaf ⟨224866,14,(.group 1 72 true)⟩))
(.branch 224894
(.leaf ⟨224880,14,(.group 1 73 true)⟩)
(.leaf ⟨224894,14,(.group 1 74 true)⟩)))))
(.branch 225020
(.branch 224964
(.branch 224936
(.branch 224922
(.leaf ⟨224908,14,(.group 1 75 true)⟩)
(.leaf ⟨224922,14,(.group 1 76 true)⟩))
(.branch 224950
(.leaf ⟨224936,14,(.group 1 77 true)⟩)
(.leaf ⟨224950,14,(.group 1 78 true)⟩)))
(.branch 224992
(.branch 224978
(.leaf ⟨224964,14,(.group 1 79 true)⟩)
(.leaf ⟨224978,14,(.group 1 80 true)⟩))
(.branch 225006
(.leaf ⟨224992,14,(.group 1 81 true)⟩)
(.leaf ⟨225006,14,(.group 1 82 true)⟩))))
(.branch 225079
(.branch 225049
(.branch 225034
(.leaf ⟨225020,14,(.group 1 83 true)⟩)
(.leaf ⟨225034,15,(.group 1 84 true)⟩))
(.branch 225064
(.leaf ⟨225049,15,(.group 1 85 true)⟩)
(.leaf ⟨225064,15,(.group 1 86 true)⟩)))
(.branch 225109
(.branch 225094
(.leaf ⟨225079,15,(.group 1 87 true)⟩)
(.leaf ⟨225094,15,(.group 1 88 true)⟩))
(.branch 225124
(.leaf ⟨225109,15,(.group 1 89 true)⟩)
(.leaf ⟨225124,15,(.group 1 90 true)⟩)))))))

theorem tree208_checked : tree208.check 224273 225139 = true := by decide +kernel

def tree209 : Tree := (.branch 225622
(.branch 225379
(.branch 225259
(.branch 225199
(.branch 225169
(.branch 225154
(.leaf ⟨225139,15,(.group 1 91 true)⟩)
(.leaf ⟨225154,15,(.group 1 92 true)⟩))
(.branch 225184
(.leaf ⟨225169,15,(.group 1 93 true)⟩)
(.leaf ⟨225184,15,(.group 1 94 true)⟩)))
(.branch 225229
(.branch 225214
(.leaf ⟨225199,15,(.group 1 95 true)⟩)
(.leaf ⟨225214,15,(.group 1 96 true)⟩))
(.branch 225244
(.leaf ⟨225229,15,(.group 1 97 true)⟩)
(.leaf ⟨225244,15,(.group 1 98 true)⟩))))
(.branch 225319
(.branch 225289
(.branch 225274
(.leaf ⟨225259,15,(.group 1 99 true)⟩)
(.leaf ⟨225274,15,(.group 1 100 true)⟩))
(.branch 225304
(.leaf ⟨225289,15,(.group 1 101 true)⟩)
(.leaf ⟨225304,15,(.group 1 102 true)⟩)))
(.branch 225349
(.branch 225334
(.leaf ⟨225319,15,(.group 1 103 true)⟩)
(.leaf ⟨225334,15,(.group 1 104 true)⟩))
(.branch 225364
(.leaf ⟨225349,15,(.group 1 105 true)⟩)
(.leaf ⟨225364,15,(.group 1 106 true)⟩)))))
(.branch 225499
(.branch 225439
(.branch 225409
(.branch 225394
(.leaf ⟨225379,15,(.group 1 107 true)⟩)
(.leaf ⟨225394,15,(.group 1 108 true)⟩))
(.branch 225424
(.leaf ⟨225409,15,(.group 1 109 true)⟩)
(.leaf ⟨225424,15,(.group 1 110 true)⟩)))
(.branch 225469
(.branch 225454
(.leaf ⟨225439,15,(.group 1 111 true)⟩)
(.leaf ⟨225454,15,(.group 1 112 true)⟩))
(.branch 225484
(.leaf ⟨225469,15,(.group 1 113 true)⟩)
(.leaf ⟨225484,15,(.group 1 114 true)⟩))))
(.branch 225559
(.branch 225529
(.branch 225514
(.leaf ⟨225499,15,(.group 1 115 true)⟩)
(.leaf ⟨225514,15,(.group 1 116 true)⟩))
(.branch 225544
(.leaf ⟨225529,15,(.group 1 117 true)⟩)
(.leaf ⟨225544,15,(.group 1 118 true)⟩)))
(.branch 225590
(.branch 225574
(.leaf ⟨225559,15,(.group 1 119 true)⟩)
(.leaf ⟨225574,16,(.group 1 120 true)⟩))
(.branch 225606
(.leaf ⟨225590,16,(.group 1 121 true)⟩)
(.leaf ⟨225606,16,(.group 1 122 true)⟩))))))
(.branch 225878
(.branch 225750
(.branch 225686
(.branch 225654
(.branch 225638
(.leaf ⟨225622,16,(.group 1 123 true)⟩)
(.leaf ⟨225638,16,(.group 1 124 true)⟩))
(.branch 225670
(.leaf ⟨225654,16,(.group 1 125 true)⟩)
(.leaf ⟨225670,16,(.group 1 126 true)⟩)))
(.branch 225718
(.branch 225702
(.leaf ⟨225686,16,(.group 1 127 true)⟩)
(.leaf ⟨225702,16,(.group 1 128 true)⟩))
(.branch 225734
(.leaf ⟨225718,16,(.group 1 129 true)⟩)
(.leaf ⟨225734,16,(.group 1 130 true)⟩))))
(.branch 225814
(.branch 225782
(.branch 225766
(.leaf ⟨225750,16,(.group 1 131 true)⟩)
(.leaf ⟨225766,16,(.group 1 132 true)⟩))
(.branch 225798
(.leaf ⟨225782,16,(.group 1 133 true)⟩)
(.leaf ⟨225798,16,(.group 1 134 true)⟩)))
(.branch 225846
(.branch 225830
(.leaf ⟨225814,16,(.group 1 135 true)⟩)
(.leaf ⟨225830,16,(.group 1 136 true)⟩))
(.branch 225862
(.leaf ⟨225846,16,(.group 1 137 true)⟩)
(.leaf ⟨225862,16,(.group 1 138 true)⟩)))))
(.branch 226006
(.branch 225942
(.branch 225910
(.branch 225894
(.leaf ⟨225878,16,(.group 1 139 true)⟩)
(.leaf ⟨225894,16,(.group 1 140 true)⟩))
(.branch 225926
(.leaf ⟨225910,16,(.group 1 141 true)⟩)
(.leaf ⟨225926,16,(.group 1 142 true)⟩)))
(.branch 225974
(.branch 225958
(.leaf ⟨225942,16,(.group 1 143 true)⟩)
(.leaf ⟨225958,16,(.group 1 144 true)⟩))
(.branch 225990
(.leaf ⟨225974,16,(.group 1 145 true)⟩)
(.leaf ⟨225990,16,(.group 1 146 true)⟩))))
(.branch 226066
(.branch 226031
(.branch 226022
(.leaf ⟨226006,16,(.group 1 147 true)⟩)
(.leaf ⟨226022,9,.trap⟩))
(.branch 226048
(.leaf ⟨226031,17,(.group 11 363 false)⟩)
(.leaf ⟨226048,18,(.group 11 489 false)⟩)))
(.branch 226088
(.branch 226078
(.leaf ⟨226066,12,(.group 11 102 false)⟩)
(.leaf ⟨226078,10,(.group 11 36 false)⟩))
(.branch 226100
(.leaf ⟨226088,12,(.group 11 92 false)⟩)
(.leaf ⟨226100,12,(.group 11 81 false)⟩)))))))

theorem tree209_checked : tree209.check 225139 226112 = true := by decide +kernel

def tree210 : Tree := (.branch 226560
(.branch 226337
(.branch 226235
(.branch 226173
(.branch 226148
(.branch 226130
(.leaf ⟨226112,18,(.group 11 480 false)⟩)
(.leaf ⟨226130,18,(.group 11 500 false)⟩))
(.branch 226157
(.leaf ⟨226148,9,(.group 11 28 false)⟩)
(.leaf ⟨226157,16,(.group 11 338 false)⟩)))
(.branch 226204
(.branch 226190
(.leaf ⟨226173,17,(.group 11 356 false)⟩)
(.leaf ⟨226190,14,(.group 11 143 false)⟩))
(.branch 226222
(.leaf ⟨226204,18,(.group 11 449 false)⟩)
(.leaf ⟨226222,13,(.group 11 155 false)⟩))))
(.branch 226290
(.branch 226262
(.branch 226251
(.leaf ⟨226235,16,(.group 11 305 false)⟩)
(.leaf ⟨226251,11,(.group 11 35 false)⟩))
(.branch 226273
(.leaf ⟨226262,11,(.group 11 57 false)⟩)
(.leaf ⟨226273,17,(.group 11 381 false)⟩)))
(.branch 226319
(.branch 226304
(.leaf ⟨226290,14,(.group 11 169 false)⟩)
(.leaf ⟨226304,15,(.group 11 219 false)⟩))
(.branch 226327
(.leaf ⟨226319,8,(.group 11 12 false)⟩)
(.leaf ⟨226327,10,(.group 11 44 false)⟩)))))
(.branch 226457
(.branch 226391
(.branch 226364
(.branch 226354
(.leaf ⟨226337,17,(.group 11 433 false)⟩)
(.leaf ⟨226354,10,(.group 11 43 false)⟩))
(.branch 226374
(.leaf ⟨226364,10,(.group 11 32 false)⟩)
(.leaf ⟨226374,17,(.group 11 430 false)⟩)))
(.branch 226424
(.branch 226409
(.leaf ⟨226391,18,(.group 11 465 false)⟩)
(.leaf ⟨226409,15,(.group 11 254 false)⟩))
(.branch 226441
(.leaf ⟨226424,17,(.group 11 374 false)⟩)
(.leaf ⟨226441,16,(.group 11 300 false)⟩))))
(.branch 226506
(.branch 226485
(.branch 226474
(.leaf ⟨226457,17,(.group 11 426 false)⟩)
(.leaf ⟨226474,11,(.group 11 51 false)⟩))
(.branch 226497
(.leaf ⟨226485,12,(.group 11 105 false)⟩)
(.leaf ⟨226497,9,(.group 11 22 false)⟩)))
(.branch 226531
(.branch 226523
(.leaf ⟨226506,17,(.group 11 418 false)⟩)
(.leaf ⟨226523,8,(.group 11 2 false)⟩))
(.branch 226543
(.leaf ⟨226531,12,(.group 11 89 false)⟩)
(.leaf ⟨226543,17,(.group 11 365 false)⟩))))))
(.branch 226782
(.branch 226669
(.branch 226615
(.branch 226594
(.branch 226578
(.leaf ⟨226560,18,(.group 11 496 false)⟩)
(.leaf ⟨226578,16,(.group 11 290 false)⟩))
(.branch 226609
(.leaf ⟨226594,15,(.group 11 221 false)⟩)
(.leaf ⟨226609,6,(.group 11 0 false)⟩)))
(.branch 226637
(.branch 226624
(.leaf ⟨226615,9,(.group 11 24 false)⟩)
(.leaf ⟨226624,13,(.group 11 148 false)⟩))
(.branch 226652
(.leaf ⟨226637,15,(.group 11 242 false)⟩)
(.leaf ⟨226652,17,(.group 11 393 false)⟩))))
(.branch 226734
(.branch 226702
(.branch 226684
(.leaf ⟨226669,15,(.group 11 256 false)⟩)
(.leaf ⟨226684,18,(.group 11 453 false)⟩))
(.branch 226718
(.leaf ⟨226702,16,(.group 11 339 false)⟩)
(.leaf ⟨226718,16,(.group 11 281 false)⟩)))
(.branch 226757
(.branch 226742
(.leaf ⟨226734,8,(.group 11 15 false)⟩)
(.leaf ⟨226742,15,(.group 11 272 false)⟩))
(.branch 226775
(.leaf ⟨226757,18,(.group 11 507 false)⟩)
(.leaf ⟨226775,7,(.group 11 4 false)⟩)))))
(.branch 226905
(.branch 226840
(.branch 226807
(.branch 226795
(.leaf ⟨226782,13,(.group 11 115 false)⟩)
(.leaf ⟨226795,12,(.group 11 83 false)⟩))
(.branch 226824
(.leaf ⟨226807,17,(.group 11 369 false)⟩)
(.leaf ⟨226824,16,(.group 11 310 false)⟩)))
(.branch 226870
(.branch 226854
(.leaf ⟨226840,14,(.group 11 200 false)⟩)
(.leaf ⟨226854,16,(.group 11 186 false)⟩))
(.branch 226888
(.leaf ⟨226870,18,(.group 11 386 false)⟩)
(.leaf ⟨226888,17,(.group 11 395 false)⟩))))
(.branch 226971
(.branch 226938
(.branch 226921
(.leaf ⟨226905,16,(.group 11 294 false)⟩)
(.leaf ⟨226921,17,(.group 11 435 false)⟩))
(.branch 226953
(.leaf ⟨226938,15,(.group 11 261 false)⟩)
(.leaf ⟨226953,18,(.group 11 255 false)⟩)))
(.branch 226998
(.branch 226985
(.leaf ⟨226971,14,(.group 11 204 false)⟩)
(.leaf ⟨226985,13,(.group 11 120 false)⟩))
(.branch 227014
(.leaf ⟨226998,16,(.group 11 343 false)⟩)
(.leaf ⟨227014,11,(.group 11 33 false)⟩)))))))

theorem tree210_checked : tree210.check 226112 227025 = true := by decide +kernel

def tree211 : Tree := (.branch 227466
(.branch 227246
(.branch 227138
(.branch 227082
(.branch 227059
(.branch 227044
(.leaf ⟨227025,19,(.group 11 508 false)⟩)
(.leaf ⟨227044,15,(.group 11 166 false)⟩))
(.branch 227070
(.leaf ⟨227059,11,(.group 11 70 false)⟩)
(.leaf ⟨227070,12,(.group 11 77 false)⟩)))
(.branch 227106
(.branch 227098
(.leaf ⟨227082,16,(.group 11 332 false)⟩)
(.leaf ⟨227098,8,(.group 11 7 false)⟩))
(.branch 227122
(.leaf ⟨227106,16,(.group 11 302 false)⟩)
(.leaf ⟨227122,16,(.group 11 331 false)⟩))))
(.branch 227196
(.branch 227167
(.branch 227152
(.leaf ⟨227138,14,(.group 11 183 false)⟩)
(.leaf ⟨227152,15,(.group 11 231 false)⟩))
(.branch 227179
(.leaf ⟨227167,12,(.group 11 93 false)⟩)
(.leaf ⟨227179,17,(.group 11 382 false)⟩)))
(.branch 227223
(.branch 227211
(.leaf ⟨227196,15,(.group 11 212 false)⟩)
(.leaf ⟨227211,12,(.group 11 99 false)⟩))
(.branch 227237
(.leaf ⟨227223,14,(.group 11 159 false)⟩)
(.leaf ⟨227237,9,(.group 11 14 false)⟩)))))
(.branch 227348
(.branch 227304
(.branch 227274
(.branch 227262
(.leaf ⟨227246,16,(.group 11 178 false)⟩)
(.leaf ⟨227262,12,(.group 11 108 false)⟩))
(.branch 227292
(.leaf ⟨227274,18,(.group 11 452 false)⟩)
(.leaf ⟨227292,12,(.group 11 101 false)⟩)))
(.branch 227327
(.branch 227314
(.leaf ⟨227304,10,(.group 11 45 false)⟩)
(.leaf ⟨227314,13,(.group 11 141 false)⟩))
(.branch 227337
(.leaf ⟨227327,10,(.group 11 39 false)⟩)
(.leaf ⟨227337,11,(.group 11 23 false)⟩))))
(.branch 227404
(.branch 227374
(.branch 227361
(.leaf ⟨227348,13,(.group 11 153 false)⟩)
(.leaf ⟨227361,13,(.group 11 63 false)⟩))
(.branch 227387
(.leaf ⟨227374,13,(.group 11 114 false)⟩)
(.leaf ⟨227387,17,(.group 11 402 false)⟩)))
(.branch 227439
(.branch 227422
(.leaf ⟨227404,18,(.group 11 434 false)⟩)
(.leaf ⟨227422,17,(.group 11 392 false)⟩))
(.branch 227451
(.leaf ⟨227439,12,(.group 11 88 false)⟩)
(.leaf ⟨227451,15,(.group 11 269 false)⟩))))))
(.branch 227714
(.branch 227602
(.branch 227534
(.branch 227502
(.branch 227483
(.leaf ⟨227466,17,(.group 11 411 false)⟩)
(.leaf ⟨227483,19,(.group 11 394 false)⟩))
(.branch 227520
(.leaf ⟨227502,18,(.group 11 466 false)⟩)
(.leaf ⟨227520,14,(.group 11 187 false)⟩)))
(.branch 227566
(.branch 227549
(.leaf ⟨227534,15,(.group 11 250 false)⟩)
(.leaf ⟨227549,17,(.group 11 397 false)⟩))
(.branch 227584
(.leaf ⟨227566,18,(.group 11 455 false)⟩)
(.leaf ⟨227584,18,(.group 11 428 false)⟩))))
(.branch 227660
(.branch 227636
(.branch 227620
(.leaf ⟨227602,18,(.group 11 505 false)⟩)
(.leaf ⟨227620,16,(.group 11 321 false)⟩))
(.branch 227643
(.leaf ⟨227636,7,(.group 11 3 false)⟩)
(.leaf ⟨227643,17,(.group 11 410 false)⟩)))
(.branch 227695
(.branch 227677
(.leaf ⟨227660,17,(.group 11 225 false)⟩)
(.leaf ⟨227677,18,(.group 11 311 false)⟩))
(.branch 227701
(.leaf ⟨227695,6,(.group 11 1 false)⟩)
(.leaf ⟨227701,13,(.group 11 95 false)⟩)))))
(.branch 227822
(.branch 227767
(.branch 227739
(.branch 227723
(.leaf ⟨227714,9,(.group 11 27 false)⟩)
(.leaf ⟨227723,16,(.group 11 287 false)⟩))
(.branch 227751
(.leaf ⟨227739,12,(.group 11 103 false)⟩)
(.leaf ⟨227751,16,(.group 11 316 false)⟩)))
(.branch 227791
(.branch 227784
(.leaf ⟨227767,17,(.group 11 441 false)⟩)
(.leaf ⟨227784,7,(.group 11 5 false)⟩))
(.branch 227806
(.leaf ⟨227791,15,(.group 11 226 false)⟩)
(.leaf ⟨227806,16,(.group 11 350 false)⟩))))
(.branch 227887
(.branch 227853
(.branch 227835
(.leaf ⟨227822,13,(.group 11 147 false)⟩)
(.leaf ⟨227835,18,(.group 11 446 false)⟩))
(.branch 227870
(.leaf ⟨227853,17,(.group 11 391 false)⟩)
(.leaf ⟨227870,17,(.group 11 253 false)⟩)))
(.branch 227910
(.branch 227898
(.leaf ⟨227887,11,(.group 11 54 false)⟩)
(.leaf ⟨227898,12,(.group 11 104 false)⟩))
(.branch 227930
(.leaf ⟨227910,20,(.group 11 425 false)⟩)
(.leaf ⟨227930,14,(.group 11 179 false)⟩)))))))

theorem tree211_checked : tree211.check 227025 227944 = true := by decide +kernel

def tree212 : Tree := (.branch 228437
(.branch 228196
(.branch 228077
(.branch 228012
(.branch 227978
(.branch 227960
(.leaf ⟨227944,16,(.group 11 317 false)⟩)
(.leaf ⟨227960,18,(.group 11 479 false)⟩))
(.branch 227994
(.leaf ⟨227978,16,(.group 11 245 false)⟩)
(.leaf ⟨227994,18,(.group 11 371 false)⟩)))
(.branch 228045
(.branch 228030
(.leaf ⟨228012,18,(.group 11 498 false)⟩)
(.leaf ⟨228030,15,(.group 11 218 false)⟩))
(.branch 228062
(.leaf ⟨228045,17,(.group 11 358 false)⟩)
(.leaf ⟨228062,15,(.group 11 271 false)⟩))))
(.branch 228136
(.branch 228101
(.branch 228093
(.leaf ⟨228077,16,(.group 11 324 false)⟩)
(.leaf ⟨228093,8,(.group 11 11 false)⟩))
(.branch 228118
(.leaf ⟨228101,17,(.group 11 396 false)⟩)
(.leaf ⟨228118,18,(.group 11 477 false)⟩)))
(.branch 228166
(.branch 228149
(.leaf ⟨228136,13,(.group 11 109 false)⟩)
(.leaf ⟨228149,17,(.group 11 366 false)⟩))
(.branch 228180
(.leaf ⟨228166,14,(.group 11 123 false)⟩)
(.leaf ⟨228180,16,(.group 11 340 false)⟩)))))
(.branch 228312
(.branch 228255
(.branch 228227
(.branch 228209
(.leaf ⟨228196,13,(.group 11 144 false)⟩)
(.leaf ⟨228209,18,(.group 11 482 false)⟩))
(.branch 228241
(.leaf ⟨228227,14,(.group 11 156 false)⟩)
(.leaf ⟨228241,14,(.group 11 194 false)⟩)))
(.branch 228285
(.branch 228272
(.leaf ⟨228255,17,(.group 11 273 false)⟩)
(.leaf ⟨228272,13,(.group 11 140 false)⟩))
(.branch 228302
(.leaf ⟨228285,17,(.group 11 298 false)⟩)
(.leaf ⟨228302,10,(.group 11 47 false)⟩))))
(.branch 228383
(.branch 228345
(.branch 228330
(.leaf ⟨228312,18,(.group 11 509 false)⟩)
(.leaf ⟨228330,15,(.group 11 244 false)⟩))
(.branch 228365
(.leaf ⟨228345,20,(.group 11 488 false)⟩)
(.leaf ⟨228365,18,(.group 11 504 false)⟩)))
(.branch 228414
(.branch 228398
(.leaf ⟨228383,15,(.group 11 236 false)⟩)
(.leaf ⟨228398,16,(.group 11 320 false)⟩))
(.branch 228425
(.leaf ⟨228414,11,(.group 11 31 false)⟩)
(.leaf ⟨228425,12,(.group 11 68 false)⟩))))))
(.branch 228690
(.branch 228556
(.branch 228491
(.branch 228464
(.branch 228449
(.leaf ⟨228437,12,(.group 11 67 false)⟩)
(.leaf ⟨228449,15,(.group 11 111 false)⟩))
(.branch 228479
(.leaf ⟨228464,15,(.group 11 274 false)⟩)
(.leaf ⟨228479,12,(.group 11 94 false)⟩)))
(.branch 228521
(.branch 228505
(.leaf ⟨228491,14,(.group 11 135 false)⟩)
(.leaf ⟨228505,16,(.group 11 227 false)⟩))
(.branch 228538
(.leaf ⟨228521,17,(.group 11 401 false)⟩)
(.leaf ⟨228538,18,(.group 11 495 false)⟩))))
(.branch 228620
(.branch 228588
(.branch 228573
(.leaf ⟨228556,17,(.group 11 413 false)⟩)
(.leaf ⟨228573,15,(.group 11 247 false)⟩))
(.branch 228604
(.leaf ⟨228588,16,(.group 11 344 false)⟩)
(.leaf ⟨228604,16,(.group 11 208 false)⟩)))
(.branch 228655
(.branch 228637
(.leaf ⟨228620,17,(.group 11 408 false)⟩)
(.leaf ⟨228637,18,(.group 11 467 false)⟩))
(.branch 228672
(.leaf ⟨228655,17,(.group 11 370 false)⟩)
(.leaf ⟨228672,18,(.group 11 457 false)⟩)))))
(.branch 228819
(.branch 228748
(.branch 228720
(.branch 228706
(.leaf ⟨228690,16,(.group 11 285 false)⟩)
(.leaf ⟨228706,14,(.group 11 188 false)⟩))
(.branch 228732
(.leaf ⟨228720,12,(.group 11 65 false)⟩)
(.leaf ⟨228732,16,(.group 11 296 false)⟩)))
(.branch 228785
(.branch 228765
(.leaf ⟨228748,17,(.group 11 400 false)⟩)
(.leaf ⟨228765,20,(.group 11 399 false)⟩))
(.branch 228803
(.leaf ⟨228785,18,(.group 11 437 false)⟩)
(.leaf ⟨228803,16,(.group 11 229 false)⟩))))
(.branch 228877
(.branch 228845
(.branch 228831
(.leaf ⟨228819,12,(.group 11 59 false)⟩)
(.leaf ⟨228831,14,(.group 11 126 false)⟩))
(.branch 228863
(.leaf ⟨228845,18,(.group 11 450 false)⟩)
(.leaf ⟨228863,14,(.group 11 197 false)⟩)))
(.branch 228905
(.branch 228894
(.leaf ⟨228877,17,(.group 11 368 false)⟩)
(.leaf ⟨228894,11,(.group 11 72 false)⟩))
(.branch 228917
(.leaf ⟨228905,12,(.group 11 71 false)⟩)
(.leaf ⟨228917,16,(.group 11 315 false)⟩)))))))

theorem tree212_checked : tree212.check 227944 228933 = true := by decide +kernel

def tree213 : Tree := (.branch 229432
(.branch 229164
(.branch 229052
(.branch 228986
(.branch 228959
(.branch 228944
(.leaf ⟨228933,11,(.group 11 61 false)⟩)
(.leaf ⟨228944,15,(.group 11 246 false)⟩))
(.branch 228970
(.leaf ⟨228959,11,(.group 11 60 false)⟩)
(.leaf ⟨228970,16,(.group 11 263 false)⟩)))
(.branch 229022
(.branch 229004
(.leaf ⟨228986,18,(.group 11 472 false)⟩)
(.leaf ⟨229004,18,(.group 11 284 false)⟩))
(.branch 229038
(.leaf ⟨229022,16,(.group 11 307 false)⟩)
(.leaf ⟨229038,14,(.group 11 149 false)⟩))))
(.branch 229100
(.branch 229075
(.branch 229067
(.leaf ⟨229052,15,(.group 11 162 false)⟩)
(.leaf ⟨229067,8,(.group 11 6 false)⟩))
(.branch 229085
(.leaf ⟨229075,10,(.group 11 30 false)⟩)
(.leaf ⟨229085,15,(.group 11 249 false)⟩)))
(.branch 229129
(.branch 229110
(.leaf ⟨229100,10,(.group 11 19 false)⟩)
(.leaf ⟨229110,19,(.group 11 459 false)⟩))
(.branch 229145
(.leaf ⟨229129,16,(.group 11 278 false)⟩)
(.leaf ⟨229145,19,(.group 11 373 false)⟩)))))
(.branch 229306
(.branch 229242
(.branch 229205
(.branch 229188
(.leaf ⟨229164,24,(.group 11 409 false)⟩)
(.leaf ⟨229188,17,(.group 11 359 false)⟩))
(.branch 229223
(.leaf ⟨229205,18,(.group 11 470 false)⟩)
(.leaf ⟨229223,19,(.group 11 351 false)⟩)))
(.branch 229277
(.branch 229261
(.leaf ⟨229242,19,(.group 11 355 false)⟩)
(.leaf ⟨229261,16,(.group 11 277 false)⟩))
(.branch 229292
(.leaf ⟨229277,15,(.group 11 234 false)⟩)
(.leaf ⟨229292,14,(.group 11 154 false)⟩))))
(.branch 229373
(.branch 229343
(.branch 229323
(.leaf ⟨229306,17,(.group 11 130 false)⟩)
(.leaf ⟨229323,20,(.group 11 306 false)⟩))
(.branch 229359
(.leaf ⟨229343,16,(.group 11 304 false)⟩)
(.leaf ⟨229359,14,(.group 11 202 false)⟩)))
(.branch 229402
(.branch 229392
(.leaf ⟨229373,19,(.group 11 473 false)⟩)
(.leaf ⟨229392,10,(.group 11 38 false)⟩))
(.branch 229420
(.leaf ⟨229402,18,(.group 11 510 false)⟩)
(.leaf ⟨229420,12,(.group 11 53 false)⟩))))))
(.branch 229672
(.branch 229556
(.branch 229491
(.branch 229465
(.branch 229448
(.leaf ⟨229432,16,(.group 11 297 false)⟩)
(.leaf ⟨229448,17,(.group 11 295 false)⟩))
(.branch 229480
(.leaf ⟨229465,15,(.group 11 270 false)⟩)
(.leaf ⟨229480,11,(.group 11 74 false)⟩)))
(.branch 229526
(.branch 229509
(.leaf ⟨229491,18,(.group 11 389 false)⟩)
(.leaf ⟨229509,17,(.group 11 260 false)⟩))
(.branch 229545
(.leaf ⟨229526,19,(.group 11 497 false)⟩)
(.leaf ⟨229545,11,(.group 11 66 false)⟩))))
(.branch 229617
(.branch 229589
(.branch 229574
(.leaf ⟨229556,18,(.group 11 487 false)⟩)
(.leaf ⟨229574,15,(.group 11 210 false)⟩))
(.branch 229600
(.leaf ⟨229589,11,(.group 11 64 false)⟩)
(.leaf ⟨229600,17,(.group 11 293 false)⟩)))
(.branch 229647
(.branch 229636
(.leaf ⟨229617,19,(.group 11 493 false)⟩)
(.leaf ⟨229636,11,(.group 11 50 false)⟩))
(.branch 229663
(.leaf ⟨229647,16,(.group 11 267 false)⟩)
(.leaf ⟨229663,9,(.group 11 9 false)⟩)))))
(.branch 229796
(.branch 229737
(.branch 229702
(.branch 229691
(.leaf ⟨229672,19,(.group 11 429 false)⟩)
(.leaf ⟨229691,11,(.group 11 46 false)⟩))
(.branch 229719
(.leaf ⟨229702,17,(.group 11 398 false)⟩)
(.leaf ⟨229719,18,(.group 11 318 false)⟩)))
(.branch 229769
(.branch 229752
(.leaf ⟨229737,15,(.group 11 136 false)⟩)
(.leaf ⟨229752,17,(.group 11 252 false)⟩))
(.branch 229781
(.leaf ⟨229769,12,(.group 11 91 false)⟩)
(.leaf ⟨229781,15,(.group 11 214 false)⟩))))
(.branch 229861
(.branch 229830
(.branch 229814
(.leaf ⟨229796,18,(.group 11 442 false)⟩)
(.leaf ⟨229814,16,(.group 11 75 false)⟩))
(.branch 229845
(.leaf ⟨229830,15,(.group 11 240 false)⟩)
(.leaf ⟨229845,16,(.group 11 175 false)⟩)))
(.branch 229894
(.branch 229879
(.leaf ⟨229861,18,(.group 11 357 false)⟩)
(.leaf ⟨229879,15,(.group 11 127 false)⟩))
(.branch 229919
(.leaf ⟨229894,25,(.group 11 405 false)⟩)
(.leaf ⟨229919,16,(.group 11 283 false)⟩)))))))

theorem tree213_checked : tree213.check 228933 229935 = true := by decide +kernel

def tree214 : Tree := (.branch 230445
(.branch 230194
(.branch 230069
(.branch 229999
(.branch 229966
(.branch 229951
(.leaf ⟨229935,16,(.group 11 52 false)⟩)
(.leaf ⟨229951,15,(.group 11 190 false)⟩))
(.branch 229984
(.leaf ⟨229966,18,(.group 11 464 false)⟩)
(.leaf ⟨229984,15,(.group 11 129 false)⟩)))
(.branch 230031
(.branch 230013
(.leaf ⟨229999,14,(.group 11 177 false)⟩)
(.leaf ⟨230013,18,(.group 11 503 false)⟩))
(.branch 230054
(.leaf ⟨230031,23,(.group 11 499 false)⟩)
(.leaf ⟨230054,15,(.group 11 163 false)⟩))))
(.branch 230130
(.branch 230099
(.branch 230086
(.leaf ⟨230069,17,(.group 11 388 false)⟩)
(.leaf ⟨230086,13,(.group 11 124 false)⟩))
(.branch 230116
(.leaf ⟨230099,17,(.group 11 361 false)⟩)
(.leaf ⟨230116,14,(.group 11 176 false)⟩)))
(.branch 230163
(.branch 230147
(.leaf ⟨230130,17,(.group 11 220 false)⟩)
(.leaf ⟨230147,16,(.group 11 276 false)⟩))
(.branch 230176
(.leaf ⟨230163,13,(.group 11 97 false)⟩)
(.leaf ⟨230176,18,(.group 11 501 false)⟩)))))
(.branch 230310
(.branch 230252
(.branch 230215
(.branch 230207
(.leaf ⟨230194,13,(.group 11 79 false)⟩)
(.leaf ⟨230207,8,(.group 11 13 false)⟩))
(.branch 230235
(.leaf ⟨230215,20,(.group 11 385 false)⟩)
(.leaf ⟨230235,17,(.group 11 407 false)⟩)))
(.branch 230277
(.branch 230265
(.leaf ⟨230252,13,(.group 11 145 false)⟩)
(.leaf ⟨230265,12,(.group 11 82 false)⟩))
(.branch 230293
(.leaf ⟨230277,16,(.group 11 167 false)⟩)
(.leaf ⟨230293,17,(.group 11 165 false)⟩))))
(.branch 230376
(.branch 230343
(.branch 230330
(.leaf ⟨230310,20,(.group 11 416 false)⟩)
(.leaf ⟨230330,13,(.group 11 150 false)⟩))
(.branch 230356
(.leaf ⟨230343,13,(.group 11 137 false)⟩)
(.leaf ⟨230356,20,(.group 11 78 false)⟩)))
(.branch 230406
(.branch 230394
(.leaf ⟨230376,18,(.group 11 447 false)⟩)
(.leaf ⟨230394,12,(.group 11 96 false)⟩))
(.branch 230427
(.leaf ⟨230406,21,(.group 11 419 false)⟩)
(.leaf ⟨230427,18,(.group 11 484 false)⟩))))))
(.branch 230728
(.branch 230581
(.branch 230507
(.branch 230476
(.branch 230462
(.leaf ⟨230445,17,(.group 11 230 false)⟩)
(.leaf ⟨230462,14,(.group 11 205 false)⟩))
(.branch 230491
(.leaf ⟨230476,15,(.group 11 192 false)⟩)
(.leaf ⟨230491,16,(.group 11 334 false)⟩)))
(.branch 230532
(.branch 230516
(.leaf ⟨230507,9,(.group 11 29 false)⟩)
(.leaf ⟨230516,16,(.group 11 333 false)⟩))
(.branch 230548
(.leaf ⟨230532,16,(.group 11 301 false)⟩)
(.leaf ⟨230548,33,(.group 11 330 false)⟩))))
(.branch 230645
(.branch 230610
(.branch 230596
(.leaf ⟨230581,15,(.group 11 215 false)⟩)
(.leaf ⟨230596,14,(.group 11 201 false)⟩))
(.branch 230632
(.leaf ⟨230610,22,(.group 11 456 false)⟩)
(.leaf ⟨230632,13,(.group 11 84 false)⟩)))
(.branch 230679
(.branch 230663
(.leaf ⟨230645,18,(.group 11 191 false)⟩)
(.leaf ⟨230663,16,(.group 11 118 false)⟩))
(.branch 230709
(.leaf ⟨230679,30,(.group 11 207 false)⟩)
(.leaf ⟨230709,19,(.group 11 448 false)⟩)))))
(.branch 230861
(.branch 230791
(.branch 230758
(.branch 230741
(.leaf ⟨230728,13,(.group 11 151 false)⟩)
(.leaf ⟨230741,17,(.group 11 372 false)⟩))
(.branch 230775
(.leaf ⟨230758,17,(.group 11 424 false)⟩)
(.leaf ⟨230775,16,(.group 11 299 false)⟩)))
(.branch 230822
(.branch 230806
(.leaf ⟨230791,15,(.group 11 56 false)⟩)
(.leaf ⟨230806,16,(.group 11 233 false)⟩))
(.branch 230839
(.leaf ⟨230822,17,(.group 11 309 false)⟩)
(.leaf ⟨230839,22,(.group 11 158 false)⟩))))
(.branch 230927
(.branch 230889
(.branch 230876
(.leaf ⟨230861,15,(.group 11 199 false)⟩)
(.leaf ⟨230876,13,(.group 11 119 false)⟩))
(.branch 230910
(.leaf ⟨230889,21,(.group 11 377 false)⟩)
(.leaf ⟨230910,17,(.group 11 436 false)⟩)))
(.branch 230955
(.branch 230936
(.leaf ⟨230927,9,(.group 11 21 false)⟩)
(.leaf ⟨230936,19,(.group 11 421 false)⟩))
(.branch 230975
(.leaf ⟨230955,20,(.group 11 327 false)⟩)
(.leaf ⟨230975,16,(.group 11 113 false)⟩)))))))

theorem tree214_checked : tree214.check 229935 230991 = true := by decide +kernel

def tree215 : Tree := (.branch 231598
(.branch 231259
(.branch 231133
(.branch 231072
(.branch 231031
(.branch 231009
(.leaf ⟨230991,18,(.group 11 461 false)⟩)
(.leaf ⟨231009,22,(.group 11 303 false)⟩))
(.branch 231049
(.leaf ⟨231031,18,(.group 11 460 false)⟩)
(.leaf ⟨231049,23,(.group 11 211 false)⟩)))
(.branch 231110
(.branch 231089
(.leaf ⟨231072,17,(.group 11 376 false)⟩)
(.leaf ⟨231089,21,(.group 11 195 false)⟩))
(.branch 231122
(.leaf ⟨231110,12,(.group 11 90 false)⟩)
(.leaf ⟨231122,11,(.group 11 34 false)⟩))))
(.branch 231198
(.branch 231163
(.branch 231149
(.leaf ⟨231133,16,(.group 11 248 false)⟩)
(.leaf ⟨231149,14,(.group 11 182 false)⟩))
(.branch 231181
(.leaf ⟨231163,18,(.group 11 491 false)⟩)
(.leaf ⟨231181,17,(.group 11 170 false)⟩)))
(.branch 231231
(.branch 231211
(.leaf ⟨231198,13,(.group 11 142 false)⟩)
(.leaf ⟨231211,20,(.group 11 451 false)⟩))
(.branch 231249
(.leaf ⟨231231,18,(.group 11 383 false)⟩)
(.leaf ⟨231249,10,(.group 11 25 false)⟩)))))
(.branch 231418
(.branch 231349
(.branch 231320
(.branch 231284
(.leaf ⟨231259,25,(.group 11 353 false)⟩)
(.leaf ⟨231284,36,(.group 11 483 false)⟩))
(.branch 231332
(.leaf ⟨231320,12,(.group 11 86 false)⟩)
(.leaf ⟨231332,17,(.group 11 375 false)⟩)))
(.branch 231381
(.branch 231361
(.leaf ⟨231349,12,(.group 11 18 false)⟩)
(.leaf ⟨231361,20,(.group 11 511 false)⟩))
(.branch 231402
(.leaf ⟨231381,21,(.group 11 292 false)⟩)
(.leaf ⟨231402,16,(.group 11 112 false)⟩))))
(.branch 231494
(.branch 231463
(.branch 231438
(.leaf ⟨231418,20,(.group 11 228 false)⟩)
(.leaf ⟨231438,25,(.group 11 420 false)⟩))
(.branch 231479
(.leaf ⟨231463,16,(.group 11 259 false)⟩)
(.leaf ⟨231479,15,(.group 11 265 false)⟩)))
(.branch 231538
(.branch 231512
(.leaf ⟨231494,18,(.group 11 257 false)⟩)
(.leaf ⟨231512,26,(.group 11 87 false)⟩))
(.branch 231576
(.leaf ⟨231538,38,(.group 11 494 false)⟩)
(.leaf ⟨231576,22,(.group 11 312 false)⟩))))))
(.branch 231879
(.branch 231747
(.branch 231684
(.branch 231639
(.branch 231615
(.leaf ⟨231598,17,(.group 11 26 false)⟩)
(.leaf ⟨231615,24,(.group 11 289 false)⟩))
(.branch 231661
(.leaf ⟨231639,22,(.group 11 134 false)⟩)
(.leaf ⟨231661,23,(.group 11 173 false)⟩)))
(.branch 231715
(.branch 231699
(.leaf ⟨231684,15,(.group 11 62 false)⟩)
(.leaf ⟨231699,16,(.group 11 157 false)⟩))
(.branch 231731
(.leaf ⟨231715,16,(.group 11 48 false)⟩)
(.leaf ⟨231731,16,(.group 11 275 false)⟩))))
(.branch 231810
(.branch 231780
(.branch 231766
(.leaf ⟨231747,19,(.group 11 40 false)⟩)
(.leaf ⟨231766,14,(.group 11 180 false)⟩))
(.branch 231797
(.leaf ⟨231780,17,(.group 11 440 false)⟩)
(.leaf ⟨231797,13,(.group 11 121 false)⟩)))
(.branch 231853
(.branch 231832
(.leaf ⟨231810,22,(.group 11 475 false)⟩)
(.leaf ⟨231832,21,(.group 11 193 false)⟩))
(.branch 231861
(.leaf ⟨231853,8,(.group 11 10 false)⟩)
(.leaf ⟨231861,18,(.group 11 222 false)⟩)))))
(.branch 232028
(.branch 231952
(.branch 231915
(.branch 231896
(.leaf ⟨231879,17,(.group 11 415 false)⟩)
(.leaf ⟨231896,19,(.group 11 342 false)⟩))
(.branch 231934
(.leaf ⟨231915,19,(.group 11 185 false)⟩)
(.leaf ⟨231934,18,(.group 11 443 false)⟩)))
(.branch 231983
(.branch 231966
(.leaf ⟨231952,14,(.group 11 206 false)⟩)
(.leaf ⟨231966,17,(.group 11 345 false)⟩))
(.branch 232009
(.leaf ⟨231983,26,(.group 11 288 false)⟩)
(.leaf ⟨232009,19,(.group 11 291 false)⟩))))
(.branch 232097
(.branch 232060
(.branch 232042
(.leaf ⟨232028,14,(.group 11 174 false)⟩)
(.leaf ⟨232042,18,(.group 11 131 false)⟩))
(.branch 232078
(.leaf ⟨232060,18,(.group 11 412 false)⟩)
(.leaf ⟨232078,19,(.group 11 20 false)⟩)))
(.branch 232130
(.branch 232111
(.leaf ⟨232097,14,(.group 11 168 false)⟩)
(.leaf ⟨232111,19,(.group 11 319 false)⟩))
(.branch 232146
(.leaf ⟨232130,16,(.group 11 209 false)⟩)
(.leaf ⟨232146,18,(.group 11 506 false)⟩)))))))

theorem tree215_checked : tree215.check 230991 232164 = true := by decide +kernel

def tree216 : Tree := (.branch 232796
(.branch 232474
(.branch 232330
(.branch 232241
(.branch 232200
(.branch 232187
(.leaf ⟨232164,23,(.group 11 404 false)⟩)
(.leaf ⟨232187,13,(.group 11 85 false)⟩))
(.branch 232221
(.leaf ⟨232200,21,(.group 11 485 false)⟩)
(.leaf ⟨232221,20,(.group 11 462 false)⟩)))
(.branch 232288
(.branch 232264
(.leaf ⟨232241,23,(.group 11 390 false)⟩)
(.leaf ⟨232264,24,(.group 11 347 false)⟩))
(.branch 232313
(.leaf ⟨232288,25,(.group 11 100 false)⟩)
(.leaf ⟨232313,17,(.group 11 239 false)⟩))))
(.branch 232392
(.branch 232357
(.branch 232342
(.leaf ⟨232330,12,(.group 11 37 false)⟩)
(.leaf ⟨232342,15,(.group 11 251 false)⟩))
(.branch 232374
(.leaf ⟨232357,17,(.group 11 379 false)⟩)
(.leaf ⟨232374,18,(.group 11 406 false)⟩)))
(.branch 232442
(.branch 232425
(.leaf ⟨232392,33,(.group 11 326 false)⟩)
(.leaf ⟨232425,17,(.group 11 58 false)⟩))
(.branch 232459
(.leaf ⟨232442,17,(.group 11 107 false)⟩)
(.leaf ⟨232459,15,(.group 11 238 false)⟩)))))
(.branch 232651
(.branch 232555
(.branch 232508
(.branch 232491
(.leaf ⟨232474,17,(.group 11 423 false)⟩)
(.leaf ⟨232491,17,(.group 11 235 false)⟩))
(.branch 232529
(.leaf ⟨232508,21,(.group 11 352 false)⟩)
(.leaf ⟨232529,26,(.group 11 490 false)⟩)))
(.branch 232589
(.branch 232571
(.leaf ⟨232555,16,(.group 11 217 false)⟩)
(.leaf ⟨232571,18,(.group 11 336 false)⟩))
(.branch 232618
(.leaf ⟨232589,29,(.group 11 476 false)⟩)
(.leaf ⟨232618,33,(.group 11 286 false)⟩))))
(.branch 232727
(.branch 232686
(.branch 232663
(.leaf ⟨232651,12,(.group 11 80 false)⟩)
(.leaf ⟨232663,23,(.group 11 314 false)⟩))
(.branch 232706
(.leaf ⟨232686,20,(.group 11 362 false)⟩)
(.leaf ⟨232706,21,(.group 11 348 false)⟩)))
(.branch 232761
(.branch 232746
(.leaf ⟨232727,19,(.group 11 308 false)⟩)
(.leaf ⟨232746,15,(.group 11 132 false)⟩))
(.branch 232774
(.leaf ⟨232761,13,(.group 11 117 false)⟩)
(.leaf ⟨232774,22,(.group 11 189 false)⟩))))))
(.branch 233118
(.branch 232958
(.branch 232868
(.branch 232832
(.branch 232815
(.leaf ⟨232796,19,(.group 11 184 false)⟩)
(.leaf ⟨232815,17,(.group 11 125 false)⟩))
(.branch 232850
(.leaf ⟨232832,18,(.group 11 367 false)⟩)
(.leaf ⟨232850,18,(.group 11 481 false)⟩)))
(.branch 232912
(.branch 232893
(.leaf ⟨232868,25,(.group 11 268 false)⟩)
(.leaf ⟨232893,19,(.group 11 454 false)⟩))
(.branch 232935
(.leaf ⟨232912,23,(.group 11 463 false)⟩)
(.leaf ⟨232935,23,(.group 11 431 false)⟩))))
(.branch 233025
(.branch 232985
(.branch 232971
(.leaf ⟨232958,13,(.group 11 55 false)⟩)
(.leaf ⟨232971,14,(.group 11 198 false)⟩))
(.branch 233007
(.leaf ⟨232985,22,(.group 11 8 false)⟩)
(.leaf ⟨233007,18,(.group 11 354 false)⟩)))
(.branch 233066
(.branch 233048
(.leaf ⟨233025,23,(.group 11 203 false)⟩)
(.leaf ⟨233048,18,(.group 11 364 false)⟩))
(.branch 233090
(.leaf ⟨233066,24,(.group 11 468 false)⟩)
(.leaf ⟨233090,28,(.group 11 380 false)⟩)))))
(.branch 233274
(.branch 233208
(.branch 233167
(.branch 233148
(.leaf ⟨233118,30,(.group 11 403 false)⟩)
(.leaf ⟨233148,19,(.group 11 502 false)⟩))
(.branch 233182
(.leaf ⟨233167,15,(.group 11 161 false)⟩)
(.leaf ⟨233182,26,(.group 11 282 false)⟩)))
(.branch 233242
(.branch 233222
(.leaf ⟨233208,14,(.group 11 172 false)⟩)
(.leaf ⟨233222,20,(.group 11 280 false)⟩))
(.branch 233260
(.leaf ⟨233242,18,(.group 11 69 false)⟩)
(.leaf ⟨233260,14,(.group 11 133 false)⟩))))
(.branch 233398
(.branch 233341
(.branch 233311
(.leaf ⟨233274,37,(.group 11 322 false)⟩)
(.leaf ⟨233311,30,(.group 11 213 false)⟩))
(.branch 233359
(.leaf ⟨233341,18,(.group 11 478 false)⟩)
(.leaf ⟨233359,39,(.group 11 323 false)⟩)))
(.branch 233467
(.branch 233416
(.leaf ⟨233398,18,(.group 11 486 false)⟩)
(.leaf ⟨233416,51,(.group 11 243 false)⟩))
(.branch 233480
(.leaf ⟨233467,13,(.group 11 98 false)⟩)
(.leaf ⟨233480,24,(.group 11 439 false)⟩)))))))

theorem tree216_checked : tree216.check 232164 233504 = true := by decide +kernel

def tree217 : Tree := (.branch 234318
(.branch 233900
(.branch 233705
(.branch 233581
(.branch 233542
(.branch 233525
(.leaf ⟨233504,21,(.group 11 471 false)⟩)
(.leaf ⟨233525,17,(.group 11 414 false)⟩))
(.branch 233559
(.leaf ⟨233542,17,(.group 11 262 false)⟩)
(.leaf ⟨233559,22,(.group 11 164 false)⟩)))
(.branch 233651
(.branch 233632
(.leaf ⟨233581,51,(.group 11 73 false)⟩)
(.leaf ⟨233632,19,(.group 11 223 false)⟩))
(.branch 233666
(.leaf ⟨233651,15,(.group 11 266 false)⟩)
(.leaf ⟨233666,39,(.group 11 110 false)⟩))))
(.branch 233791
(.branch 233748
(.branch 233721
(.leaf ⟨233705,16,(.group 11 171 false)⟩)
(.leaf ⟨233721,27,(.group 11 329 false)⟩))
(.branch 233765
(.leaf ⟨233748,17,(.group 11 237 false)⟩)
(.leaf ⟨233765,26,(.group 11 417 false)⟩)))
(.branch 233851
(.branch 233811
(.leaf ⟨233791,20,(.group 11 458 false)⟩)
(.leaf ⟨233811,40,(.group 11 325 false)⟩))
(.branch 233875
(.leaf ⟨233851,24,(.group 11 106 false)⟩)
(.leaf ⟨233875,25,(.group 11 444 false)⟩)))))
(.branch 234112
(.branch 233997
(.branch 233962
(.branch 233917
(.leaf ⟨233900,17,(.group 11 438 false)⟩)
(.leaf ⟨233917,45,(.group 11 313 false)⟩))
(.branch 233980
(.leaf ⟨233962,18,(.group 11 387 false)⟩)
(.leaf ⟨233980,17,(.group 11 138 false)⟩)))
(.branch 234051
(.branch 234033
(.leaf ⟨233997,36,(.group 11 128 false)⟩)
(.leaf ⟨234033,18,(.group 11 349 false)⟩))
(.branch 234090
(.leaf ⟨234051,39,(.group 11 469 false)⟩)
(.leaf ⟨234090,22,(.group 11 181 false)⟩))))
(.branch 234219
(.branch 234162
(.branch 234139
(.leaf ⟨234112,27,(.group 11 49 false)⟩)
(.leaf ⟨234139,23,(.group 11 341 false)⟩))
(.branch 234201
(.leaf ⟨234162,39,(.group 11 378 false)⟩)
(.leaf ⟨234201,18,(.group 11 384 false)⟩)))
(.branch 234261
(.branch 234238
(.leaf ⟨234219,19,(.group 11 335 false)⟩)
(.leaf ⟨234238,23,(.group 11 346 false)⟩))
(.branch 234291
(.leaf ⟨234261,30,(.group 11 360 false)⟩)
(.leaf ⟨234291,27,(.group 11 196 false)⟩))))))
(.branch 234866
(.branch 234565
(.branch 234398
(.branch 234367
(.branch 234349
(.leaf ⟨234318,31,(.group 11 160 false)⟩)
(.leaf ⟨234349,18,(.group 11 492 false)⟩))
(.branch 234381
(.leaf ⟨234367,14,(.group 11 42 false)⟩)
(.leaf ⟨234381,17,(.group 11 116 false)⟩)))
(.branch 234479
(.branch 234416
(.leaf ⟨234398,18,(.group 11 422 false)⟩)
(.leaf ⟨234416,63,(.group 11 216 false)⟩))
(.branch 234550
(.leaf ⟨234479,71,(.group 11 279 false)⟩)
(.leaf ⟨234550,15,(.group 11 241 false)⟩))))
(.branch 234711
(.branch 234680
(.branch 234639
(.leaf ⟨234565,74,(.group 11 432 false)⟩)
(.leaf ⟨234639,41,(.group 11 427 false)⟩))
(.branch 234693
(.leaf ⟨234680,13,(.group 11 41 false)⟩)
(.leaf ⟨234693,18,(.group 11 258 false)⟩)))
(.branch 234822
(.branch 234742
(.leaf ⟨234711,31,(.group 11 474 false)⟩)
(.leaf ⟨234742,80,(.group 11 232 false)⟩))
(.branch 234849
(.leaf ⟨234822,27,(.group 11 445 false)⟩)
(.leaf ⟨234849,17,(.group 11 16 false)⟩)))))
(.branch 235400
(.branch 235140
(.branch 234941
(.branch 234894
(.leaf ⟨234866,28,(.group 11 152 false)⟩)
(.leaf ⟨234894,47,(.group 11 264 false)⟩))
(.branch 235009
(.leaf ⟨234941,68,(.group 11 337 false)⟩)
(.leaf ⟨235009,131,(.group 11 122 false)⟩)))
(.branch 235281
(.branch 235243
(.leaf ⟨235140,103,(.group 11 76 false)⟩)
(.leaf ⟨235243,38,(.group 11 139 false)⟩))
(.branch 235349
(.leaf ⟨235281,68,(.group 11 224 false)⟩)
(.leaf ⟨235349,51,(.group 11 146 false)⟩))))
(.branch 235632
(.branch 235618
(.branch 235602
(.leaf ⟨235400,202,(.group 11 17 false)⟩)
(.leaf ⟨235602,16,(.group 11 328 false)⟩))
(.branch 235625
(.leaf ⟨235618,7,(.group 12 0 false)⟩)
(.leaf ⟨235625,7,(.group 12 1 false)⟩)))
(.branch 235646
(.branch 235639
(.leaf ⟨235632,7,(.group 12 2 false)⟩)
(.leaf ⟨235639,7,(.group 12 3 false)⟩))
(.branch 235653
(.leaf ⟨235646,7,(.group 12 4 false)⟩)
(.leaf ⟨235653,7,(.group 12 5 false)⟩)))))))

theorem tree217_checked : tree217.check 233504 235660 = true := by decide +kernel

def tree218 : Tree := (.branch 235884
(.branch 235772
(.branch 235716
(.branch 235688
(.branch 235674
(.branch 235667
(.leaf ⟨235660,7,(.group 12 6 false)⟩)
(.leaf ⟨235667,7,(.group 12 7 false)⟩))
(.branch 235681
(.leaf ⟨235674,7,(.group 12 8 false)⟩)
(.leaf ⟨235681,7,(.group 12 9 false)⟩)))
(.branch 235702
(.branch 235695
(.leaf ⟨235688,7,(.group 12 10 false)⟩)
(.leaf ⟨235695,7,(.group 12 11 false)⟩))
(.branch 235709
(.leaf ⟨235702,7,(.group 12 12 false)⟩)
(.leaf ⟨235709,7,(.group 12 13 false)⟩))))
(.branch 235744
(.branch 235730
(.branch 235723
(.leaf ⟨235716,7,(.group 12 14 false)⟩)
(.leaf ⟨235723,7,(.group 12 15 false)⟩))
(.branch 235737
(.leaf ⟨235730,7,(.group 12 16 false)⟩)
(.leaf ⟨235737,7,(.group 12 17 false)⟩)))
(.branch 235758
(.branch 235751
(.leaf ⟨235744,7,(.group 12 18 false)⟩)
(.leaf ⟨235751,7,(.group 12 19 false)⟩))
(.branch 235765
(.leaf ⟨235758,7,(.group 12 20 false)⟩)
(.leaf ⟨235765,7,(.group 12 21 false)⟩)))))
(.branch 235828
(.branch 235800
(.branch 235786
(.branch 235779
(.leaf ⟨235772,7,(.group 12 22 false)⟩)
(.leaf ⟨235779,7,(.group 12 23 false)⟩))
(.branch 235793
(.leaf ⟨235786,7,(.group 12 24 false)⟩)
(.leaf ⟨235793,7,(.group 12 25 false)⟩)))
(.branch 235814
(.branch 235807
(.leaf ⟨235800,7,(.group 12 26 false)⟩)
(.leaf ⟨235807,7,(.group 12 27 false)⟩))
(.branch 235821
(.leaf ⟨235814,7,(.group 12 28 false)⟩)
(.leaf ⟨235821,7,(.group 12 29 false)⟩))))
(.branch 235856
(.branch 235842
(.branch 235835
(.leaf ⟨235828,7,(.group 12 30 false)⟩)
(.leaf ⟨235835,7,(.group 12 31 false)⟩))
(.branch 235849
(.leaf ⟨235842,7,(.group 12 32 false)⟩)
(.leaf ⟨235849,7,(.group 12 33 false)⟩)))
(.branch 235870
(.branch 235863
(.leaf ⟨235856,7,(.group 12 34 false)⟩)
(.leaf ⟨235863,7,(.group 12 35 false)⟩))
(.branch 235877
(.leaf ⟨235870,7,(.group 12 36 false)⟩)
(.leaf ⟨235877,7,(.group 12 37 false)⟩))))))
(.branch 235996
(.branch 235940
(.branch 235912
(.branch 235898
(.branch 235891
(.leaf ⟨235884,7,(.group 12 38 false)⟩)
(.leaf ⟨235891,7,(.group 12 39 false)⟩))
(.branch 235905
(.leaf ⟨235898,7,(.group 12 40 false)⟩)
(.leaf ⟨235905,7,(.group 12 41 false)⟩)))
(.branch 235926
(.branch 235919
(.leaf ⟨235912,7,(.group 12 42 false)⟩)
(.leaf ⟨235919,7,(.group 12 43 false)⟩))
(.branch 235933
(.leaf ⟨235926,7,(.group 12 44 false)⟩)
(.leaf ⟨235933,7,(.group 12 45 false)⟩))))
(.branch 235968
(.branch 235954
(.branch 235947
(.leaf ⟨235940,7,(.group 12 46 false)⟩)
(.leaf ⟨235947,7,(.group 12 47 false)⟩))
(.branch 235961
(.leaf ⟨235954,7,(.group 12 48 false)⟩)
(.leaf ⟨235961,7,(.group 12 49 false)⟩)))
(.branch 235982
(.branch 235975
(.leaf ⟨235968,7,(.group 12 50 false)⟩)
(.leaf ⟨235975,7,(.group 12 51 false)⟩))
(.branch 235989
(.leaf ⟨235982,7,(.group 12 52 false)⟩)
(.leaf ⟨235989,7,(.group 12 53 false)⟩)))))
(.branch 236052
(.branch 236024
(.branch 236010
(.branch 236003
(.leaf ⟨235996,7,(.group 12 54 false)⟩)
(.leaf ⟨236003,7,(.group 12 55 false)⟩))
(.branch 236017
(.leaf ⟨236010,7,(.group 12 56 false)⟩)
(.leaf ⟨236017,7,(.group 12 57 false)⟩)))
(.branch 236038
(.branch 236031
(.leaf ⟨236024,7,(.group 12 58 false)⟩)
(.leaf ⟨236031,7,(.group 12 59 false)⟩))
(.branch 236045
(.leaf ⟨236038,7,(.group 12 60 false)⟩)
(.leaf ⟨236045,7,(.group 12 61 false)⟩))))
(.branch 236080
(.branch 236066
(.branch 236059
(.leaf ⟨236052,7,(.group 12 62 false)⟩)
(.leaf ⟨236059,7,(.group 12 63 false)⟩))
(.branch 236073
(.leaf ⟨236066,7,(.group 12 64 false)⟩)
(.leaf ⟨236073,7,(.group 12 65 false)⟩)))
(.branch 236094
(.branch 236087
(.leaf ⟨236080,7,(.group 12 66 false)⟩)
(.leaf ⟨236087,7,(.group 12 67 false)⟩))
(.branch 236101
(.leaf ⟨236094,7,(.group 12 68 false)⟩)
(.leaf ⟨236101,7,(.group 12 69 false)⟩)))))))

theorem tree218_checked : tree218.check 235660 236108 = true := by decide +kernel

def tree219 : Tree := (.branch 236332
(.branch 236220
(.branch 236164
(.branch 236136
(.branch 236122
(.branch 236115
(.leaf ⟨236108,7,(.group 12 70 false)⟩)
(.leaf ⟨236115,7,(.group 12 71 false)⟩))
(.branch 236129
(.leaf ⟨236122,7,(.group 12 72 false)⟩)
(.leaf ⟨236129,7,(.group 12 73 false)⟩)))
(.branch 236150
(.branch 236143
(.leaf ⟨236136,7,(.group 12 74 false)⟩)
(.leaf ⟨236143,7,(.group 12 75 false)⟩))
(.branch 236157
(.leaf ⟨236150,7,(.group 12 76 false)⟩)
(.leaf ⟨236157,7,(.group 12 77 false)⟩))))
(.branch 236192
(.branch 236178
(.branch 236171
(.leaf ⟨236164,7,(.group 12 78 false)⟩)
(.leaf ⟨236171,7,(.group 12 79 false)⟩))
(.branch 236185
(.leaf ⟨236178,7,(.group 12 80 false)⟩)
(.leaf ⟨236185,7,(.group 12 81 false)⟩)))
(.branch 236206
(.branch 236199
(.leaf ⟨236192,7,(.group 12 82 false)⟩)
(.leaf ⟨236199,7,(.group 12 83 false)⟩))
(.branch 236213
(.leaf ⟨236206,7,(.group 12 84 false)⟩)
(.leaf ⟨236213,7,(.group 12 85 false)⟩)))))
(.branch 236276
(.branch 236248
(.branch 236234
(.branch 236227
(.leaf ⟨236220,7,(.group 12 86 false)⟩)
(.leaf ⟨236227,7,(.group 12 87 false)⟩))
(.branch 236241
(.leaf ⟨236234,7,(.group 12 88 false)⟩)
(.leaf ⟨236241,7,(.group 12 89 false)⟩)))
(.branch 236262
(.branch 236255
(.leaf ⟨236248,7,(.group 12 90 false)⟩)
(.leaf ⟨236255,7,(.group 12 91 false)⟩))
(.branch 236269
(.leaf ⟨236262,7,(.group 12 92 false)⟩)
(.leaf ⟨236269,7,(.group 12 93 false)⟩))))
(.branch 236304
(.branch 236290
(.branch 236283
(.leaf ⟨236276,7,(.group 12 94 false)⟩)
(.leaf ⟨236283,7,(.group 12 95 false)⟩))
(.branch 236297
(.leaf ⟨236290,7,(.group 12 96 false)⟩)
(.leaf ⟨236297,7,(.group 12 97 false)⟩)))
(.branch 236318
(.branch 236311
(.leaf ⟨236304,7,(.group 12 98 false)⟩)
(.leaf ⟨236311,7,(.group 12 99 false)⟩))
(.branch 236325
(.leaf ⟨236318,7,(.group 12 100 false)⟩)
(.leaf ⟨236325,7,(.group 12 101 false)⟩))))))
(.branch 236444
(.branch 236388
(.branch 236360
(.branch 236346
(.branch 236339
(.leaf ⟨236332,7,(.group 12 102 false)⟩)
(.leaf ⟨236339,7,(.group 12 103 false)⟩))
(.branch 236353
(.leaf ⟨236346,7,(.group 12 104 false)⟩)
(.leaf ⟨236353,7,(.group 12 105 false)⟩)))
(.branch 236374
(.branch 236367
(.leaf ⟨236360,7,(.group 12 106 false)⟩)
(.leaf ⟨236367,7,(.group 12 107 false)⟩))
(.branch 236381
(.leaf ⟨236374,7,(.group 12 108 false)⟩)
(.leaf ⟨236381,7,(.group 12 109 false)⟩))))
(.branch 236416
(.branch 236402
(.branch 236395
(.leaf ⟨236388,7,(.group 12 110 false)⟩)
(.leaf ⟨236395,7,(.group 12 111 false)⟩))
(.branch 236409
(.leaf ⟨236402,7,(.group 12 112 false)⟩)
(.leaf ⟨236409,7,(.group 12 113 false)⟩)))
(.branch 236430
(.branch 236423
(.leaf ⟨236416,7,(.group 12 114 false)⟩)
(.leaf ⟨236423,7,(.group 12 115 false)⟩))
(.branch 236437
(.leaf ⟨236430,7,(.group 12 116 false)⟩)
(.leaf ⟨236437,7,(.group 12 117 false)⟩)))))
(.branch 236500
(.branch 236472
(.branch 236458
(.branch 236451
(.leaf ⟨236444,7,(.group 12 118 false)⟩)
(.leaf ⟨236451,7,(.group 12 119 false)⟩))
(.branch 236465
(.leaf ⟨236458,7,(.group 12 120 false)⟩)
(.leaf ⟨236465,7,(.group 12 121 false)⟩)))
(.branch 236486
(.branch 236479
(.leaf ⟨236472,7,(.group 12 122 false)⟩)
(.leaf ⟨236479,7,(.group 12 123 false)⟩))
(.branch 236493
(.leaf ⟨236486,7,(.group 12 124 false)⟩)
(.leaf ⟨236493,7,(.group 12 125 false)⟩))))
(.branch 236528
(.branch 236514
(.branch 236507
(.leaf ⟨236500,7,(.group 12 126 false)⟩)
(.leaf ⟨236507,7,(.group 12 127 false)⟩))
(.branch 236521
(.leaf ⟨236514,7,(.group 12 128 false)⟩)
(.leaf ⟨236521,7,(.group 12 129 false)⟩)))
(.branch 236542
(.branch 236535
(.leaf ⟨236528,7,(.group 12 130 false)⟩)
(.leaf ⟨236535,7,(.group 12 131 false)⟩))
(.branch 236549
(.leaf ⟨236542,7,(.group 12 132 false)⟩)
(.leaf ⟨236549,7,(.group 12 133 false)⟩)))))))

theorem tree219_checked : tree219.check 236108 236556 = true := by decide +kernel

def tree220 : Tree := (.branch 236818
(.branch 236673
(.branch 236612
(.branch 236584
(.branch 236570
(.branch 236563
(.leaf ⟨236556,7,(.group 12 134 false)⟩)
(.leaf ⟨236563,7,(.group 12 135 false)⟩))
(.branch 236577
(.leaf ⟨236570,7,(.group 12 136 false)⟩)
(.leaf ⟨236577,7,(.group 12 137 false)⟩)))
(.branch 236598
(.branch 236591
(.leaf ⟨236584,7,(.group 12 138 false)⟩)
(.leaf ⟨236591,7,(.group 12 139 false)⟩))
(.branch 236605
(.leaf ⟨236598,7,(.group 12 140 false)⟩)
(.leaf ⟨236605,7,(.group 12 141 false)⟩))))
(.branch 236641
(.branch 236626
(.branch 236619
(.leaf ⟨236612,7,(.group 12 142 false)⟩)
(.leaf ⟨236619,7,(.group 12 143 false)⟩))
(.branch 236633
(.leaf ⟨236626,7,(.group 12 144 false)⟩)
(.leaf ⟨236633,8,(.group 12 145 false)⟩)))
(.branch 236657
(.branch 236649
(.leaf ⟨236641,8,(.group 12 146 false)⟩)
(.leaf ⟨236649,8,(.group 12 147 false)⟩))
(.branch 236665
(.leaf ⟨236657,8,(.group 12 148 false)⟩)
(.leaf ⟨236665,8,(.group 12 149 false)⟩)))))
(.branch 236742
(.branch 236706
(.branch 236689
(.branch 236681
(.leaf ⟨236673,8,(.group 12 150 false)⟩)
(.leaf ⟨236681,8,(.group 12 151 false)⟩))
(.branch 236697
(.leaf ⟨236689,8,(.group 12 152 false)⟩)
(.leaf ⟨236697,9,(.group 12 153 false)⟩)))
(.branch 236724
(.branch 236715
(.leaf ⟨236706,9,(.group 12 154 false)⟩)
(.leaf ⟨236715,9,(.group 12 155 false)⟩))
(.branch 236733
(.leaf ⟨236724,9,(.group 12 156 false)⟩)
(.leaf ⟨236733,9,(.group 12 157 false)⟩))))
(.branch 236778
(.branch 236760
(.branch 236751
(.leaf ⟨236742,9,(.group 12 158 false)⟩)
(.leaf ⟨236751,9,(.group 12 159 false)⟩))
(.branch 236769
(.leaf ⟨236760,9,(.group 12 160 false)⟩)
(.leaf ⟨236769,9,(.group 12 161 false)⟩)))
(.branch 236798
(.branch 236788
(.leaf ⟨236778,10,(.group 12 162 false)⟩)
(.leaf ⟨236788,10,(.group 12 163 false)⟩))
(.branch 236808
(.leaf ⟨236798,10,(.group 12 164 false)⟩)
(.leaf ⟨236808,10,(.group 12 165 false)⟩))))))
(.branch 236984
(.branch 236898
(.branch 236858
(.branch 236838
(.branch 236828
(.leaf ⟨236818,10,(.group 12 166 false)⟩)
(.leaf ⟨236828,10,(.group 12 167 false)⟩))
(.branch 236848
(.leaf ⟨236838,10,(.group 12 168 false)⟩)
(.leaf ⟨236848,10,(.group 12 169 false)⟩)))
(.branch 236878
(.branch 236868
(.leaf ⟨236858,10,(.group 12 170 false)⟩)
(.leaf ⟨236868,10,(.group 12 171 false)⟩))
(.branch 236888
(.leaf ⟨236878,10,(.group 12 172 false)⟩)
(.leaf ⟨236888,10,(.group 12 173 false)⟩))))
(.branch 236940
(.branch 236918
(.branch 236908
(.leaf ⟨236898,10,(.group 12 174 false)⟩)
(.leaf ⟨236908,10,(.group 12 175 false)⟩))
(.branch 236929
(.leaf ⟨236918,11,(.group 12 176 false)⟩)
(.leaf ⟨236929,11,(.group 12 177 false)⟩)))
(.branch 236962
(.branch 236951
(.leaf ⟨236940,11,(.group 12 178 false)⟩)
(.leaf ⟨236951,11,(.group 12 179 false)⟩))
(.branch 236973
(.leaf ⟨236962,11,(.group 12 180 false)⟩)
(.leaf ⟨236973,11,(.group 12 181 false)⟩)))))
(.branch 237072
(.branch 237028
(.branch 237006
(.branch 236995
(.leaf ⟨236984,11,(.group 12 182 false)⟩)
(.leaf ⟨236995,11,(.group 12 183 false)⟩))
(.branch 237017
(.leaf ⟨237006,11,(.group 12 184 false)⟩)
(.leaf ⟨237017,11,(.group 12 185 false)⟩)))
(.branch 237050
(.branch 237039
(.leaf ⟨237028,11,(.group 12 186 false)⟩)
(.leaf ⟨237039,11,(.group 12 187 false)⟩))
(.branch 237061
(.leaf ⟨237050,11,(.group 12 188 false)⟩)
(.leaf ⟨237061,11,(.group 12 189 false)⟩))))
(.branch 237116
(.branch 237094
(.branch 237083
(.leaf ⟨237072,11,(.group 12 190 false)⟩)
(.leaf ⟨237083,11,(.group 12 191 false)⟩))
(.branch 237105
(.leaf ⟨237094,11,(.group 12 192 false)⟩)
(.leaf ⟨237105,11,(.group 12 193 false)⟩)))
(.branch 237138
(.branch 237127
(.leaf ⟨237116,11,(.group 12 194 false)⟩)
(.leaf ⟨237127,11,(.group 12 195 false)⟩))
(.branch 237150
(.leaf ⟨237138,12,(.group 12 196 false)⟩)
(.leaf ⟨237150,12,(.group 12 197 false)⟩)))))))

theorem tree220_checked : tree220.check 236556 237162 = true := by decide +kernel

def tree221 : Tree := (.branch 237553
(.branch 237354
(.branch 237258
(.branch 237210
(.branch 237186
(.branch 237174
(.leaf ⟨237162,12,(.group 12 198 false)⟩)
(.leaf ⟨237174,12,(.group 12 199 false)⟩))
(.branch 237198
(.leaf ⟨237186,12,(.group 12 200 false)⟩)
(.leaf ⟨237198,12,(.group 12 201 false)⟩)))
(.branch 237234
(.branch 237222
(.leaf ⟨237210,12,(.group 12 202 false)⟩)
(.leaf ⟨237222,12,(.group 12 203 false)⟩))
(.branch 237246
(.leaf ⟨237234,12,(.group 12 204 false)⟩)
(.leaf ⟨237246,12,(.group 12 205 false)⟩))))
(.branch 237306
(.branch 237282
(.branch 237270
(.leaf ⟨237258,12,(.group 12 206 false)⟩)
(.leaf ⟨237270,12,(.group 12 207 false)⟩))
(.branch 237294
(.leaf ⟨237282,12,(.group 12 208 false)⟩)
(.leaf ⟨237294,12,(.group 12 209 false)⟩)))
(.branch 237330
(.branch 237318
(.leaf ⟨237306,12,(.group 12 210 false)⟩)
(.leaf ⟨237318,12,(.group 12 211 false)⟩))
(.branch 237342
(.leaf ⟨237330,12,(.group 12 212 false)⟩)
(.leaf ⟨237342,12,(.group 12 213 false)⟩)))))
(.branch 237450
(.branch 237402
(.branch 237378
(.branch 237366
(.leaf ⟨237354,12,(.group 12 214 false)⟩)
(.leaf ⟨237366,12,(.group 12 215 false)⟩))
(.branch 237390
(.leaf ⟨237378,12,(.group 12 216 false)⟩)
(.leaf ⟨237390,12,(.group 12 217 false)⟩)))
(.branch 237426
(.branch 237414
(.leaf ⟨237402,12,(.group 12 218 false)⟩)
(.leaf ⟨237414,12,(.group 12 219 false)⟩))
(.branch 237438
(.leaf ⟨237426,12,(.group 12 220 false)⟩)
(.leaf ⟨237438,12,(.group 12 221 false)⟩))))
(.branch 237501
(.branch 237475
(.branch 237462
(.leaf ⟨237450,12,(.group 12 222 false)⟩)
(.leaf ⟨237462,13,(.group 12 223 false)⟩))
(.branch 237488
(.leaf ⟨237475,13,(.group 12 224 false)⟩)
(.leaf ⟨237488,13,(.group 12 225 false)⟩)))
(.branch 237527
(.branch 237514
(.leaf ⟨237501,13,(.group 12 226 false)⟩)
(.leaf ⟨237514,13,(.group 12 227 false)⟩))
(.branch 237540
(.leaf ⟨237527,13,(.group 12 228 false)⟩)
(.leaf ⟨237540,13,(.group 12 229 false)⟩))))))
(.branch 237761
(.branch 237657
(.branch 237605
(.branch 237579
(.branch 237566
(.leaf ⟨237553,13,(.group 12 230 false)⟩)
(.leaf ⟨237566,13,(.group 12 231 false)⟩))
(.branch 237592
(.leaf ⟨237579,13,(.group 12 232 false)⟩)
(.leaf ⟨237592,13,(.group 12 233 false)⟩)))
(.branch 237631
(.branch 237618
(.leaf ⟨237605,13,(.group 12 234 false)⟩)
(.leaf ⟨237618,13,(.group 12 235 false)⟩))
(.branch 237644
(.leaf ⟨237631,13,(.group 12 236 false)⟩)
(.leaf ⟨237644,13,(.group 12 237 false)⟩))))
(.branch 237709
(.branch 237683
(.branch 237670
(.leaf ⟨237657,13,(.group 12 238 false)⟩)
(.leaf ⟨237670,13,(.group 12 239 false)⟩))
(.branch 237696
(.leaf ⟨237683,13,(.group 12 240 false)⟩)
(.leaf ⟨237696,13,(.group 12 241 false)⟩)))
(.branch 237735
(.branch 237722
(.leaf ⟨237709,13,(.group 12 242 false)⟩)
(.leaf ⟨237722,13,(.group 12 243 false)⟩))
(.branch 237748
(.leaf ⟨237735,13,(.group 12 244 false)⟩)
(.leaf ⟨237748,13,(.group 12 245 false)⟩)))))
(.branch 237865
(.branch 237813
(.branch 237787
(.branch 237774
(.leaf ⟨237761,13,(.group 12 246 false)⟩)
(.leaf ⟨237774,13,(.group 12 247 false)⟩))
(.branch 237800
(.leaf ⟨237787,13,(.group 12 248 false)⟩)
(.leaf ⟨237800,13,(.group 12 249 false)⟩)))
(.branch 237839
(.branch 237826
(.leaf ⟨237813,13,(.group 12 250 false)⟩)
(.leaf ⟨237826,13,(.group 12 251 false)⟩))
(.branch 237852
(.leaf ⟨237839,13,(.group 12 252 false)⟩)
(.leaf ⟨237852,13,(.group 12 253 false)⟩))))
(.branch 237917
(.branch 237891
(.branch 237878
(.leaf ⟨237865,13,(.group 12 254 false)⟩)
(.leaf ⟨237878,13,(.group 12 255 false)⟩))
(.branch 237904
(.leaf ⟨237891,13,(.group 12 256 false)⟩)
(.leaf ⟨237904,13,(.group 12 257 false)⟩)))
(.branch 237945
(.branch 237931
(.leaf ⟨237917,14,(.group 12 258 false)⟩)
(.leaf ⟨237931,14,(.group 12 259 false)⟩))
(.branch 237959
(.leaf ⟨237945,14,(.group 12 260 false)⟩)
(.leaf ⟨237959,14,(.group 12 261 false)⟩)))))))

theorem tree221_checked : tree221.check 237162 237973 = true := by decide +kernel

def tree222 : Tree := (.branch 238421
(.branch 238197
(.branch 238085
(.branch 238029
(.branch 238001
(.branch 237987
(.leaf ⟨237973,14,(.group 12 262 false)⟩)
(.leaf ⟨237987,14,(.group 12 263 false)⟩))
(.branch 238015
(.leaf ⟨238001,14,(.group 12 264 false)⟩)
(.leaf ⟨238015,14,(.group 12 265 false)⟩)))
(.branch 238057
(.branch 238043
(.leaf ⟨238029,14,(.group 12 266 false)⟩)
(.leaf ⟨238043,14,(.group 12 267 false)⟩))
(.branch 238071
(.leaf ⟨238057,14,(.group 12 268 false)⟩)
(.leaf ⟨238071,14,(.group 12 269 false)⟩))))
(.branch 238141
(.branch 238113
(.branch 238099
(.leaf ⟨238085,14,(.group 12 270 false)⟩)
(.leaf ⟨238099,14,(.group 12 271 false)⟩))
(.branch 238127
(.leaf ⟨238113,14,(.group 12 272 false)⟩)
(.leaf ⟨238127,14,(.group 12 273 false)⟩)))
(.branch 238169
(.branch 238155
(.leaf ⟨238141,14,(.group 12 274 false)⟩)
(.leaf ⟨238155,14,(.group 12 275 false)⟩))
(.branch 238183
(.leaf ⟨238169,14,(.group 12 276 false)⟩)
(.leaf ⟨238183,14,(.group 12 277 false)⟩)))))
(.branch 238309
(.branch 238253
(.branch 238225
(.branch 238211
(.leaf ⟨238197,14,(.group 12 278 false)⟩)
(.leaf ⟨238211,14,(.group 12 279 false)⟩))
(.branch 238239
(.leaf ⟨238225,14,(.group 12 280 false)⟩)
(.leaf ⟨238239,14,(.group 12 281 false)⟩)))
(.branch 238281
(.branch 238267
(.leaf ⟨238253,14,(.group 12 282 false)⟩)
(.leaf ⟨238267,14,(.group 12 283 false)⟩))
(.branch 238295
(.leaf ⟨238281,14,(.group 12 284 false)⟩)
(.leaf ⟨238295,14,(.group 12 285 false)⟩))))
(.branch 238365
(.branch 238337
(.branch 238323
(.leaf ⟨238309,14,(.group 12 286 false)⟩)
(.leaf ⟨238323,14,(.group 12 287 false)⟩))
(.branch 238351
(.leaf ⟨238337,14,(.group 12 288 false)⟩)
(.leaf ⟨238351,14,(.group 12 289 false)⟩)))
(.branch 238393
(.branch 238379
(.leaf ⟨238365,14,(.group 12 290 false)⟩)
(.leaf ⟨238379,14,(.group 12 291 false)⟩))
(.branch 238407
(.leaf ⟨238393,14,(.group 12 292 false)⟩)
(.leaf ⟨238407,14,(.group 12 293 false)⟩))))))
(.branch 238653
(.branch 238533
(.branch 238477
(.branch 238449
(.branch 238435
(.leaf ⟨238421,14,(.group 12 294 false)⟩)
(.leaf ⟨238435,14,(.group 12 295 false)⟩))
(.branch 238463
(.leaf ⟨238449,14,(.group 12 296 false)⟩)
(.leaf ⟨238463,14,(.group 12 297 false)⟩)))
(.branch 238505
(.branch 238491
(.leaf ⟨238477,14,(.group 12 298 false)⟩)
(.leaf ⟨238491,14,(.group 12 299 false)⟩))
(.branch 238519
(.leaf ⟨238505,14,(.group 12 300 false)⟩)
(.leaf ⟨238519,14,(.group 12 301 false)⟩))))
(.branch 238593
(.branch 238563
(.branch 238548
(.leaf ⟨238533,15,(.group 12 302 false)⟩)
(.leaf ⟨238548,15,(.group 12 303 false)⟩))
(.branch 238578
(.leaf ⟨238563,15,(.group 12 304 false)⟩)
(.leaf ⟨238578,15,(.group 12 305 false)⟩)))
(.branch 238623
(.branch 238608
(.leaf ⟨238593,15,(.group 12 306 false)⟩)
(.leaf ⟨238608,15,(.group 12 307 false)⟩))
(.branch 238638
(.leaf ⟨238623,15,(.group 12 308 false)⟩)
(.leaf ⟨238638,15,(.group 12 309 false)⟩)))))
(.branch 238773
(.branch 238713
(.branch 238683
(.branch 238668
(.leaf ⟨238653,15,(.group 12 310 false)⟩)
(.leaf ⟨238668,15,(.group 12 311 false)⟩))
(.branch 238698
(.leaf ⟨238683,15,(.group 12 312 false)⟩)
(.leaf ⟨238698,15,(.group 12 313 false)⟩)))
(.branch 238743
(.branch 238728
(.leaf ⟨238713,15,(.group 12 314 false)⟩)
(.leaf ⟨238728,15,(.group 12 315 false)⟩))
(.branch 238758
(.leaf ⟨238743,15,(.group 12 316 false)⟩)
(.leaf ⟨238758,15,(.group 12 317 false)⟩))))
(.branch 238833
(.branch 238803
(.branch 238788
(.leaf ⟨238773,15,(.group 12 318 false)⟩)
(.leaf ⟨238788,15,(.group 12 319 false)⟩))
(.branch 238818
(.leaf ⟨238803,15,(.group 12 320 false)⟩)
(.leaf ⟨238818,15,(.group 12 321 false)⟩)))
(.branch 238863
(.branch 238848
(.leaf ⟨238833,15,(.group 12 322 false)⟩)
(.leaf ⟨238848,15,(.group 12 323 false)⟩))
(.branch 238878
(.leaf ⟨238863,15,(.group 12 324 false)⟩)
(.leaf ⟨238878,15,(.group 12 325 false)⟩)))))))

theorem tree222_checked : tree222.check 237973 238893 = true := by decide +kernel

def tree223 : Tree := (.branch 239375
(.branch 239133
(.branch 239013
(.branch 238953
(.branch 238923
(.branch 238908
(.leaf ⟨238893,15,(.group 12 326 false)⟩)
(.leaf ⟨238908,15,(.group 12 327 false)⟩))
(.branch 238938
(.leaf ⟨238923,15,(.group 12 328 false)⟩)
(.leaf ⟨238938,15,(.group 12 329 false)⟩)))
(.branch 238983
(.branch 238968
(.leaf ⟨238953,15,(.group 12 330 false)⟩)
(.leaf ⟨238968,15,(.group 12 331 false)⟩))
(.branch 238998
(.leaf ⟨238983,15,(.group 12 332 false)⟩)
(.leaf ⟨238998,15,(.group 12 333 false)⟩))))
(.branch 239073
(.branch 239043
(.branch 239028
(.leaf ⟨239013,15,(.group 12 334 false)⟩)
(.leaf ⟨239028,15,(.group 12 335 false)⟩))
(.branch 239058
(.leaf ⟨239043,15,(.group 12 336 false)⟩)
(.leaf ⟨239058,15,(.group 12 337 false)⟩)))
(.branch 239103
(.branch 239088
(.leaf ⟨239073,15,(.group 12 338 false)⟩)
(.leaf ⟨239088,15,(.group 12 339 false)⟩))
(.branch 239118
(.leaf ⟨239103,15,(.group 12 340 false)⟩)
(.leaf ⟨239118,15,(.group 12 341 false)⟩)))))
(.branch 239253
(.branch 239193
(.branch 239163
(.branch 239148
(.leaf ⟨239133,15,(.group 12 342 false)⟩)
(.leaf ⟨239148,15,(.group 12 343 false)⟩))
(.branch 239178
(.leaf ⟨239163,15,(.group 12 344 false)⟩)
(.leaf ⟨239178,15,(.group 12 345 false)⟩)))
(.branch 239223
(.branch 239208
(.leaf ⟨239193,15,(.group 12 346 false)⟩)
(.leaf ⟨239208,15,(.group 12 347 false)⟩))
(.branch 239238
(.leaf ⟨239223,15,(.group 12 348 false)⟩)
(.leaf ⟨239238,15,(.group 12 349 false)⟩))))
(.branch 239313
(.branch 239283
(.branch 239268
(.leaf ⟨239253,15,(.group 12 350 false)⟩)
(.leaf ⟨239268,15,(.group 12 351 false)⟩))
(.branch 239298
(.leaf ⟨239283,15,(.group 12 352 false)⟩)
(.leaf ⟨239298,15,(.group 12 353 false)⟩)))
(.branch 239343
(.branch 239328
(.leaf ⟨239313,15,(.group 12 354 false)⟩)
(.leaf ⟨239328,15,(.group 12 355 false)⟩))
(.branch 239359
(.leaf ⟨239343,16,(.group 12 356 false)⟩)
(.leaf ⟨239359,16,(.group 12 357 false)⟩))))))
(.branch 239631
(.branch 239503
(.branch 239439
(.branch 239407
(.branch 239391
(.leaf ⟨239375,16,(.group 12 358 false)⟩)
(.leaf ⟨239391,16,(.group 12 359 false)⟩))
(.branch 239423
(.leaf ⟨239407,16,(.group 12 360 false)⟩)
(.leaf ⟨239423,16,(.group 12 361 false)⟩)))
(.branch 239471
(.branch 239455
(.leaf ⟨239439,16,(.group 12 362 false)⟩)
(.leaf ⟨239455,16,(.group 12 363 false)⟩))
(.branch 239487
(.leaf ⟨239471,16,(.group 12 364 false)⟩)
(.leaf ⟨239487,16,(.group 12 365 false)⟩))))
(.branch 239567
(.branch 239535
(.branch 239519
(.leaf ⟨239503,16,(.group 12 366 false)⟩)
(.leaf ⟨239519,16,(.group 12 367 false)⟩))
(.branch 239551
(.leaf ⟨239535,16,(.group 12 368 false)⟩)
(.leaf ⟨239551,16,(.group 12 369 false)⟩)))
(.branch 239599
(.branch 239583
(.leaf ⟨239567,16,(.group 12 370 false)⟩)
(.leaf ⟨239583,16,(.group 12 371 false)⟩))
(.branch 239615
(.leaf ⟨239599,16,(.group 12 372 false)⟩)
(.leaf ⟨239615,16,(.group 12 373 false)⟩)))))
(.branch 239759
(.branch 239695
(.branch 239663
(.branch 239647
(.leaf ⟨239631,16,(.group 12 374 false)⟩)
(.leaf ⟨239647,16,(.group 12 375 false)⟩))
(.branch 239679
(.leaf ⟨239663,16,(.group 12 376 false)⟩)
(.leaf ⟨239679,16,(.group 12 377 false)⟩)))
(.branch 239727
(.branch 239711
(.leaf ⟨239695,16,(.group 12 378 false)⟩)
(.leaf ⟨239711,16,(.group 12 379 false)⟩))
(.branch 239743
(.leaf ⟨239727,16,(.group 12 380 false)⟩)
(.leaf ⟨239743,16,(.group 12 381 false)⟩))))
(.branch 239823
(.branch 239791
(.branch 239775
(.leaf ⟨239759,16,(.group 12 382 false)⟩)
(.leaf ⟨239775,16,(.group 12 383 false)⟩))
(.branch 239807
(.leaf ⟨239791,16,(.group 12 384 false)⟩)
(.leaf ⟨239807,16,(.group 12 385 false)⟩)))
(.branch 239855
(.branch 239839
(.leaf ⟨239823,16,(.group 12 386 false)⟩)
(.leaf ⟨239839,16,(.group 12 387 false)⟩))
(.branch 239871
(.leaf ⟨239855,16,(.group 12 388 false)⟩)
(.leaf ⟨239871,16,(.group 12 389 false)⟩)))))))

theorem tree223_checked : tree223.check 238893 239887 = true := by decide +kernel

def tree224 : Tree := (.branch 240399
(.branch 240143
(.branch 240015
(.branch 239951
(.branch 239919
(.branch 239903
(.leaf ⟨239887,16,(.group 12 390 false)⟩)
(.leaf ⟨239903,16,(.group 12 391 false)⟩))
(.branch 239935
(.leaf ⟨239919,16,(.group 12 392 false)⟩)
(.leaf ⟨239935,16,(.group 12 393 false)⟩)))
(.branch 239983
(.branch 239967
(.leaf ⟨239951,16,(.group 12 394 false)⟩)
(.leaf ⟨239967,16,(.group 12 395 false)⟩))
(.branch 239999
(.leaf ⟨239983,16,(.group 12 396 false)⟩)
(.leaf ⟨239999,16,(.group 12 397 false)⟩))))
(.branch 240079
(.branch 240047
(.branch 240031
(.leaf ⟨240015,16,(.group 12 398 false)⟩)
(.leaf ⟨240031,16,(.group 12 399 false)⟩))
(.branch 240063
(.leaf ⟨240047,16,(.group 12 400 false)⟩)
(.leaf ⟨240063,16,(.group 12 401 false)⟩)))
(.branch 240111
(.branch 240095
(.leaf ⟨240079,16,(.group 12 402 false)⟩)
(.leaf ⟨240095,16,(.group 12 403 false)⟩))
(.branch 240127
(.leaf ⟨240111,16,(.group 12 404 false)⟩)
(.leaf ⟨240127,16,(.group 12 405 false)⟩)))))
(.branch 240271
(.branch 240207
(.branch 240175
(.branch 240159
(.leaf ⟨240143,16,(.group 12 406 false)⟩)
(.leaf ⟨240159,16,(.group 12 407 false)⟩))
(.branch 240191
(.leaf ⟨240175,16,(.group 12 408 false)⟩)
(.leaf ⟨240191,16,(.group 12 409 false)⟩)))
(.branch 240239
(.branch 240223
(.leaf ⟨240207,16,(.group 12 410 false)⟩)
(.leaf ⟨240223,16,(.group 12 411 false)⟩))
(.branch 240255
(.leaf ⟨240239,16,(.group 12 412 false)⟩)
(.leaf ⟨240255,16,(.group 12 413 false)⟩))))
(.branch 240335
(.branch 240303
(.branch 240287
(.leaf ⟨240271,16,(.group 12 414 false)⟩)
(.leaf ⟨240287,16,(.group 12 415 false)⟩))
(.branch 240319
(.leaf ⟨240303,16,(.group 12 416 false)⟩)
(.leaf ⟨240319,16,(.group 12 417 false)⟩)))
(.branch 240367
(.branch 240351
(.leaf ⟨240335,16,(.group 12 418 false)⟩)
(.leaf ⟨240351,16,(.group 12 419 false)⟩))
(.branch 240383
(.leaf ⟨240367,16,(.group 12 420 false)⟩)
(.leaf ⟨240383,16,(.group 12 421 false)⟩))))))
(.branch 240664
(.branch 240528
(.branch 240463
(.branch 240431
(.branch 240415
(.leaf ⟨240399,16,(.group 12 422 false)⟩)
(.leaf ⟨240415,16,(.group 12 423 false)⟩))
(.branch 240447
(.leaf ⟨240431,16,(.group 12 424 false)⟩)
(.leaf ⟨240447,16,(.group 12 425 false)⟩)))
(.branch 240495
(.branch 240479
(.leaf ⟨240463,16,(.group 12 426 false)⟩)
(.leaf ⟨240479,16,(.group 12 427 false)⟩))
(.branch 240511
(.leaf ⟨240495,16,(.group 12 428 false)⟩)
(.leaf ⟨240511,17,(.group 12 429 false)⟩))))
(.branch 240596
(.branch 240562
(.branch 240545
(.leaf ⟨240528,17,(.group 12 430 false)⟩)
(.leaf ⟨240545,17,(.group 12 431 false)⟩))
(.branch 240579
(.leaf ⟨240562,17,(.group 12 432 false)⟩)
(.leaf ⟨240579,17,(.group 12 433 false)⟩)))
(.branch 240630
(.branch 240613
(.leaf ⟨240596,17,(.group 12 434 false)⟩)
(.leaf ⟨240613,17,(.group 12 435 false)⟩))
(.branch 240647
(.leaf ⟨240630,17,(.group 12 436 false)⟩)
(.leaf ⟨240647,17,(.group 12 437 false)⟩)))))
(.branch 240800
(.branch 240732
(.branch 240698
(.branch 240681
(.leaf ⟨240664,17,(.group 12 438 false)⟩)
(.leaf ⟨240681,17,(.group 12 439 false)⟩))
(.branch 240715
(.leaf ⟨240698,17,(.group 12 440 false)⟩)
(.leaf ⟨240715,17,(.group 12 441 false)⟩)))
(.branch 240766
(.branch 240749
(.leaf ⟨240732,17,(.group 12 442 false)⟩)
(.leaf ⟨240749,17,(.group 12 443 false)⟩))
(.branch 240783
(.leaf ⟨240766,17,(.group 12 444 false)⟩)
(.leaf ⟨240783,17,(.group 12 445 false)⟩))))
(.branch 240868
(.branch 240834
(.branch 240817
(.leaf ⟨240800,17,(.group 12 446 false)⟩)
(.leaf ⟨240817,17,(.group 12 447 false)⟩))
(.branch 240851
(.leaf ⟨240834,17,(.group 12 448 false)⟩)
(.leaf ⟨240851,17,(.group 12 449 false)⟩)))
(.branch 240902
(.branch 240885
(.leaf ⟨240868,17,(.group 12 450 false)⟩)
(.leaf ⟨240885,17,(.group 12 451 false)⟩))
(.branch 240919
(.leaf ⟨240902,17,(.group 12 452 false)⟩)
(.leaf ⟨240919,17,(.group 12 453 false)⟩)))))))

theorem tree224_checked : tree224.check 239887 240936 = true := by decide +kernel

def tree225 : Tree := (.branch 241480
(.branch 241208
(.branch 241072
(.branch 241004
(.branch 240970
(.branch 240953
(.leaf ⟨240936,17,(.group 12 454 false)⟩)
(.leaf ⟨240953,17,(.group 12 455 false)⟩))
(.branch 240987
(.leaf ⟨240970,17,(.group 12 456 false)⟩)
(.leaf ⟨240987,17,(.group 12 457 false)⟩)))
(.branch 241038
(.branch 241021
(.leaf ⟨241004,17,(.group 12 458 false)⟩)
(.leaf ⟨241021,17,(.group 12 459 false)⟩))
(.branch 241055
(.leaf ⟨241038,17,(.group 12 460 false)⟩)
(.leaf ⟨241055,17,(.group 12 461 false)⟩))))
(.branch 241140
(.branch 241106
(.branch 241089
(.leaf ⟨241072,17,(.group 12 462 false)⟩)
(.leaf ⟨241089,17,(.group 12 463 false)⟩))
(.branch 241123
(.leaf ⟨241106,17,(.group 12 464 false)⟩)
(.leaf ⟨241123,17,(.group 12 465 false)⟩)))
(.branch 241174
(.branch 241157
(.leaf ⟨241140,17,(.group 12 466 false)⟩)
(.leaf ⟨241157,17,(.group 12 467 false)⟩))
(.branch 241191
(.leaf ⟨241174,17,(.group 12 468 false)⟩)
(.leaf ⟨241191,17,(.group 12 469 false)⟩)))))
(.branch 241344
(.branch 241276
(.branch 241242
(.branch 241225
(.leaf ⟨241208,17,(.group 12 470 false)⟩)
(.leaf ⟨241225,17,(.group 12 471 false)⟩))
(.branch 241259
(.leaf ⟨241242,17,(.group 12 472 false)⟩)
(.leaf ⟨241259,17,(.group 12 473 false)⟩)))
(.branch 241310
(.branch 241293
(.leaf ⟨241276,17,(.group 12 474 false)⟩)
(.leaf ⟨241293,17,(.group 12 475 false)⟩))
(.branch 241327
(.leaf ⟨241310,17,(.group 12 476 false)⟩)
(.leaf ⟨241327,17,(.group 12 477 false)⟩))))
(.branch 241412
(.branch 241378
(.branch 241361
(.leaf ⟨241344,17,(.group 12 478 false)⟩)
(.leaf ⟨241361,17,(.group 12 479 false)⟩))
(.branch 241395
(.leaf ⟨241378,17,(.group 12 480 false)⟩)
(.leaf ⟨241395,17,(.group 12 481 false)⟩)))
(.branch 241446
(.branch 241429
(.leaf ⟨241412,17,(.group 12 482 false)⟩)
(.leaf ⟨241429,17,(.group 12 483 false)⟩))
(.branch 241463
(.leaf ⟨241446,17,(.group 12 484 false)⟩)
(.leaf ⟨241463,17,(.group 12 485 false)⟩))))))
(.branch 241752
(.branch 241616
(.branch 241548
(.branch 241514
(.branch 241497
(.leaf ⟨241480,17,(.group 12 486 false)⟩)
(.leaf ⟨241497,17,(.group 12 487 false)⟩))
(.branch 241531
(.leaf ⟨241514,17,(.group 12 488 false)⟩)
(.leaf ⟨241531,17,(.group 12 489 false)⟩)))
(.branch 241582
(.branch 241565
(.leaf ⟨241548,17,(.group 12 490 false)⟩)
(.leaf ⟨241565,17,(.group 12 491 false)⟩))
(.branch 241599
(.leaf ⟨241582,17,(.group 12 492 false)⟩)
(.leaf ⟨241599,17,(.group 12 493 false)⟩))))
(.branch 241684
(.branch 241650
(.branch 241633
(.leaf ⟨241616,17,(.group 12 494 false)⟩)
(.leaf ⟨241633,17,(.group 12 495 false)⟩))
(.branch 241667
(.leaf ⟨241650,17,(.group 12 496 false)⟩)
(.leaf ⟨241667,17,(.group 12 497 false)⟩)))
(.branch 241718
(.branch 241701
(.leaf ⟨241684,17,(.group 12 498 false)⟩)
(.leaf ⟨241701,17,(.group 12 499 false)⟩))
(.branch 241735
(.leaf ⟨241718,17,(.group 12 500 false)⟩)
(.leaf ⟨241735,17,(.group 12 501 false)⟩)))))
(.branch 241892
(.branch 241820
(.branch 241786
(.branch 241769
(.leaf ⟨241752,17,(.group 12 502 false)⟩)
(.leaf ⟨241769,17,(.group 12 503 false)⟩))
(.branch 241803
(.leaf ⟨241786,17,(.group 12 504 false)⟩)
(.leaf ⟨241803,17,(.group 12 505 false)⟩)))
(.branch 241856
(.branch 241838
(.leaf ⟨241820,18,(.group 12 506 false)⟩)
(.leaf ⟨241838,18,(.group 12 507 false)⟩))
(.branch 241874
(.leaf ⟨241856,18,(.group 12 508 false)⟩)
(.leaf ⟨241874,18,(.group 12 509 false)⟩))))
(.branch 241964
(.branch 241928
(.branch 241910
(.leaf ⟨241892,18,(.group 12 510 false)⟩)
(.leaf ⟨241910,18,(.group 12 511 false)⟩))
(.branch 241946
(.leaf ⟨241928,18,(.group 12 512 false)⟩)
(.leaf ⟨241946,18,(.group 12 513 false)⟩)))
(.branch 242000
(.branch 241982
(.leaf ⟨241964,18,(.group 12 514 false)⟩)
(.leaf ⟨241982,18,(.group 12 515 false)⟩))
(.branch 242018
(.leaf ⟨242000,18,(.group 12 516 false)⟩)
(.leaf ⟨242018,18,(.group 12 517 false)⟩)))))))

theorem tree225_checked : tree225.check 240936 242036 = true := by decide +kernel

def tree226 : Tree := (.branch 242612
(.branch 242324
(.branch 242180
(.branch 242108
(.branch 242072
(.branch 242054
(.leaf ⟨242036,18,(.group 12 518 false)⟩)
(.leaf ⟨242054,18,(.group 12 519 false)⟩))
(.branch 242090
(.leaf ⟨242072,18,(.group 12 520 false)⟩)
(.leaf ⟨242090,18,(.group 12 521 false)⟩)))
(.branch 242144
(.branch 242126
(.leaf ⟨242108,18,(.group 12 522 false)⟩)
(.leaf ⟨242126,18,(.group 12 523 false)⟩))
(.branch 242162
(.leaf ⟨242144,18,(.group 12 524 false)⟩)
(.leaf ⟨242162,18,(.group 12 525 false)⟩))))
(.branch 242252
(.branch 242216
(.branch 242198
(.leaf ⟨242180,18,(.group 12 526 false)⟩)
(.leaf ⟨242198,18,(.group 12 527 false)⟩))
(.branch 242234
(.leaf ⟨242216,18,(.group 12 528 false)⟩)
(.leaf ⟨242234,18,(.group 12 529 false)⟩)))
(.branch 242288
(.branch 242270
(.leaf ⟨242252,18,(.group 12 530 false)⟩)
(.leaf ⟨242270,18,(.group 12 531 false)⟩))
(.branch 242306
(.leaf ⟨242288,18,(.group 12 532 false)⟩)
(.leaf ⟨242306,18,(.group 12 533 false)⟩)))))
(.branch 242468
(.branch 242396
(.branch 242360
(.branch 242342
(.leaf ⟨242324,18,(.group 12 534 false)⟩)
(.leaf ⟨242342,18,(.group 12 535 false)⟩))
(.branch 242378
(.leaf ⟨242360,18,(.group 12 536 false)⟩)
(.leaf ⟨242378,18,(.group 12 537 false)⟩)))
(.branch 242432
(.branch 242414
(.leaf ⟨242396,18,(.group 12 538 false)⟩)
(.leaf ⟨242414,18,(.group 12 539 false)⟩))
(.branch 242450
(.leaf ⟨242432,18,(.group 12 540 false)⟩)
(.leaf ⟨242450,18,(.group 12 541 false)⟩))))
(.branch 242540
(.branch 242504
(.branch 242486
(.leaf ⟨242468,18,(.group 12 542 false)⟩)
(.leaf ⟨242486,18,(.group 12 543 false)⟩))
(.branch 242522
(.leaf ⟨242504,18,(.group 12 544 false)⟩)
(.leaf ⟨242522,18,(.group 12 545 false)⟩)))
(.branch 242576
(.branch 242558
(.leaf ⟨242540,18,(.group 12 546 false)⟩)
(.leaf ⟨242558,18,(.group 12 547 false)⟩))
(.branch 242594
(.leaf ⟨242576,18,(.group 12 548 false)⟩)
(.leaf ⟨242594,18,(.group 12 549 false)⟩))))))
(.branch 242900
(.branch 242756
(.branch 242684
(.branch 242648
(.branch 242630
(.leaf ⟨242612,18,(.group 12 550 false)⟩)
(.leaf ⟨242630,18,(.group 12 551 false)⟩))
(.branch 242666
(.leaf ⟨242648,18,(.group 12 552 false)⟩)
(.leaf ⟨242666,18,(.group 12 553 false)⟩)))
(.branch 242720
(.branch 242702
(.leaf ⟨242684,18,(.group 12 554 false)⟩)
(.leaf ⟨242702,18,(.group 12 555 false)⟩))
(.branch 242738
(.leaf ⟨242720,18,(.group 12 556 false)⟩)
(.leaf ⟨242738,18,(.group 12 557 false)⟩))))
(.branch 242828
(.branch 242792
(.branch 242774
(.leaf ⟨242756,18,(.group 12 558 false)⟩)
(.leaf ⟨242774,18,(.group 12 559 false)⟩))
(.branch 242810
(.leaf ⟨242792,18,(.group 12 560 false)⟩)
(.leaf ⟨242810,18,(.group 12 561 false)⟩)))
(.branch 242864
(.branch 242846
(.leaf ⟨242828,18,(.group 12 562 false)⟩)
(.leaf ⟨242846,18,(.group 12 563 false)⟩))
(.branch 242882
(.leaf ⟨242864,18,(.group 12 564 false)⟩)
(.leaf ⟨242882,18,(.group 12 565 false)⟩)))))
(.branch 243044
(.branch 242972
(.branch 242936
(.branch 242918
(.leaf ⟨242900,18,(.group 12 566 false)⟩)
(.leaf ⟨242918,18,(.group 12 567 false)⟩))
(.branch 242954
(.leaf ⟨242936,18,(.group 12 568 false)⟩)
(.leaf ⟨242954,18,(.group 12 569 false)⟩)))
(.branch 243008
(.branch 242990
(.leaf ⟨242972,18,(.group 12 570 false)⟩)
(.leaf ⟨242990,18,(.group 12 571 false)⟩))
(.branch 243026
(.leaf ⟨243008,18,(.group 12 572 false)⟩)
(.leaf ⟨243026,18,(.group 12 573 false)⟩))))
(.branch 243116
(.branch 243080
(.branch 243062
(.leaf ⟨243044,18,(.group 12 574 false)⟩)
(.leaf ⟨243062,18,(.group 12 575 false)⟩))
(.branch 243098
(.leaf ⟨243080,18,(.group 12 576 false)⟩)
(.leaf ⟨243098,18,(.group 12 577 false)⟩)))
(.branch 243152
(.branch 243134
(.leaf ⟨243116,18,(.group 12 578 false)⟩)
(.leaf ⟨243134,18,(.group 12 579 false)⟩))
(.branch 243170
(.leaf ⟨243152,18,(.group 12 580 false)⟩)
(.leaf ⟨243170,18,(.group 12 581 false)⟩)))))))

theorem tree226_checked : tree226.check 242036 243188 = true := by decide +kernel

def tree227 : Tree := (.branch 243782
(.branch 243478
(.branch 243332
(.branch 243260
(.branch 243224
(.branch 243206
(.leaf ⟨243188,18,(.group 12 582 false)⟩)
(.leaf ⟨243206,18,(.group 12 583 false)⟩))
(.branch 243242
(.leaf ⟨243224,18,(.group 12 584 false)⟩)
(.leaf ⟨243242,18,(.group 12 585 false)⟩)))
(.branch 243296
(.branch 243278
(.leaf ⟨243260,18,(.group 12 586 false)⟩)
(.leaf ⟨243278,18,(.group 12 587 false)⟩))
(.branch 243314
(.leaf ⟨243296,18,(.group 12 588 false)⟩)
(.leaf ⟨243314,18,(.group 12 589 false)⟩))))
(.branch 243404
(.branch 243368
(.branch 243350
(.leaf ⟨243332,18,(.group 12 590 false)⟩)
(.leaf ⟨243350,18,(.group 12 591 false)⟩))
(.branch 243386
(.leaf ⟨243368,18,(.group 12 592 false)⟩)
(.leaf ⟨243386,18,(.group 12 593 false)⟩)))
(.branch 243440
(.branch 243422
(.leaf ⟨243404,18,(.group 12 594 false)⟩)
(.leaf ⟨243422,18,(.group 12 595 false)⟩))
(.branch 243459
(.leaf ⟨243440,19,(.group 12 596 false)⟩)
(.leaf ⟨243459,19,(.group 12 597 false)⟩)))))
(.branch 243630
(.branch 243554
(.branch 243516
(.branch 243497
(.leaf ⟨243478,19,(.group 12 598 false)⟩)
(.leaf ⟨243497,19,(.group 12 599 false)⟩))
(.branch 243535
(.leaf ⟨243516,19,(.group 12 600 false)⟩)
(.leaf ⟨243535,19,(.group 12 601 false)⟩)))
(.branch 243592
(.branch 243573
(.leaf ⟨243554,19,(.group 12 602 false)⟩)
(.leaf ⟨243573,19,(.group 12 603 false)⟩))
(.branch 243611
(.leaf ⟨243592,19,(.group 12 604 false)⟩)
(.leaf ⟨243611,19,(.group 12 605 false)⟩))))
(.branch 243706
(.branch 243668
(.branch 243649
(.leaf ⟨243630,19,(.group 12 606 false)⟩)
(.leaf ⟨243649,19,(.group 12 607 false)⟩))
(.branch 243687
(.leaf ⟨243668,19,(.group 12 608 false)⟩)
(.leaf ⟨243687,19,(.group 12 609 false)⟩)))
(.branch 243744
(.branch 243725
(.leaf ⟨243706,19,(.group 12 610 false)⟩)
(.leaf ⟨243725,19,(.group 12 611 false)⟩))
(.branch 243763
(.leaf ⟨243744,19,(.group 12 612 false)⟩)
(.leaf ⟨243763,19,(.group 12 613 false)⟩))))))
(.branch 244086
(.branch 243934
(.branch 243858
(.branch 243820
(.branch 243801
(.leaf ⟨243782,19,(.group 12 614 false)⟩)
(.leaf ⟨243801,19,(.group 12 615 false)⟩))
(.branch 243839
(.leaf ⟨243820,19,(.group 12 616 false)⟩)
(.leaf ⟨243839,19,(.group 12 617 false)⟩)))
(.branch 243896
(.branch 243877
(.leaf ⟨243858,19,(.group 12 618 false)⟩)
(.leaf ⟨243877,19,(.group 12 619 false)⟩))
(.branch 243915
(.leaf ⟨243896,19,(.group 12 620 false)⟩)
(.leaf ⟨243915,19,(.group 12 621 false)⟩))))
(.branch 244010
(.branch 243972
(.branch 243953
(.leaf ⟨243934,19,(.group 12 622 false)⟩)
(.leaf ⟨243953,19,(.group 12 623 false)⟩))
(.branch 243991
(.leaf ⟨243972,19,(.group 12 624 false)⟩)
(.leaf ⟨243991,19,(.group 12 625 false)⟩)))
(.branch 244048
(.branch 244029
(.leaf ⟨244010,19,(.group 12 626 false)⟩)
(.leaf ⟨244029,19,(.group 12 627 false)⟩))
(.branch 244067
(.leaf ⟨244048,19,(.group 12 628 false)⟩)
(.leaf ⟨244067,19,(.group 12 629 false)⟩)))))
(.branch 244238
(.branch 244162
(.branch 244124
(.branch 244105
(.leaf ⟨244086,19,(.group 12 630 false)⟩)
(.leaf ⟨244105,19,(.group 12 631 false)⟩))
(.branch 244143
(.leaf ⟨244124,19,(.group 12 632 false)⟩)
(.leaf ⟨244143,19,(.group 12 633 false)⟩)))
(.branch 244200
(.branch 244181
(.leaf ⟨244162,19,(.group 12 634 false)⟩)
(.leaf ⟨244181,19,(.group 12 635 false)⟩))
(.branch 244219
(.leaf ⟨244200,19,(.group 12 636 false)⟩)
(.leaf ⟨244219,19,(.group 12 637 false)⟩))))
(.branch 244314
(.branch 244276
(.branch 244257
(.leaf ⟨244238,19,(.group 12 638 false)⟩)
(.leaf ⟨244257,19,(.group 12 639 false)⟩))
(.branch 244295
(.leaf ⟨244276,19,(.group 12 640 false)⟩)
(.leaf ⟨244295,19,(.group 12 641 false)⟩)))
(.branch 244352
(.branch 244333
(.leaf ⟨244314,19,(.group 12 642 false)⟩)
(.leaf ⟨244333,19,(.group 12 643 false)⟩))
(.branch 244371
(.leaf ⟨244352,19,(.group 12 644 false)⟩)
(.leaf ⟨244371,19,(.group 12 645 false)⟩)))))))

theorem tree227_checked : tree227.check 243188 244390 = true := by decide +kernel

def tree228 : Tree := (.branch 244998
(.branch 244694
(.branch 244542
(.branch 244466
(.branch 244428
(.branch 244409
(.leaf ⟨244390,19,(.group 12 646 false)⟩)
(.leaf ⟨244409,19,(.group 12 647 false)⟩))
(.branch 244447
(.leaf ⟨244428,19,(.group 12 648 false)⟩)
(.leaf ⟨244447,19,(.group 12 649 false)⟩)))
(.branch 244504
(.branch 244485
(.leaf ⟨244466,19,(.group 12 650 false)⟩)
(.leaf ⟨244485,19,(.group 12 651 false)⟩))
(.branch 244523
(.leaf ⟨244504,19,(.group 12 652 false)⟩)
(.leaf ⟨244523,19,(.group 12 653 false)⟩))))
(.branch 244618
(.branch 244580
(.branch 244561
(.leaf ⟨244542,19,(.group 12 654 false)⟩)
(.leaf ⟨244561,19,(.group 12 655 false)⟩))
(.branch 244599
(.leaf ⟨244580,19,(.group 12 656 false)⟩)
(.leaf ⟨244599,19,(.group 12 657 false)⟩)))
(.branch 244656
(.branch 244637
(.leaf ⟨244618,19,(.group 12 658 false)⟩)
(.leaf ⟨244637,19,(.group 12 659 false)⟩))
(.branch 244675
(.leaf ⟨244656,19,(.group 12 660 false)⟩)
(.leaf ⟨244675,19,(.group 12 661 false)⟩)))))
(.branch 244846
(.branch 244770
(.branch 244732
(.branch 244713
(.leaf ⟨244694,19,(.group 12 662 false)⟩)
(.leaf ⟨244713,19,(.group 12 663 false)⟩))
(.branch 244751
(.leaf ⟨244732,19,(.group 12 664 false)⟩)
(.leaf ⟨244751,19,(.group 12 665 false)⟩)))
(.branch 244808
(.branch 244789
(.leaf ⟨244770,19,(.group 12 666 false)⟩)
(.leaf ⟨244789,19,(.group 12 667 false)⟩))
(.branch 244827
(.leaf ⟨244808,19,(.group 12 668 false)⟩)
(.leaf ⟨244827,19,(.group 12 669 false)⟩))))
(.branch 244922
(.branch 244884
(.branch 244865
(.leaf ⟨244846,19,(.group 12 670 false)⟩)
(.leaf ⟨244865,19,(.group 12 671 false)⟩))
(.branch 244903
(.leaf ⟨244884,19,(.group 12 672 false)⟩)
(.leaf ⟨244903,19,(.group 12 673 false)⟩)))
(.branch 244960
(.branch 244941
(.leaf ⟨244922,19,(.group 12 674 false)⟩)
(.leaf ⟨244941,19,(.group 12 675 false)⟩))
(.branch 244979
(.leaf ⟨244960,19,(.group 12 676 false)⟩)
(.leaf ⟨244979,19,(.group 12 677 false)⟩))))))
(.branch 245302
(.branch 245150
(.branch 245074
(.branch 245036
(.branch 245017
(.leaf ⟨244998,19,(.group 12 678 false)⟩)
(.leaf ⟨245017,19,(.group 12 679 false)⟩))
(.branch 245055
(.leaf ⟨245036,19,(.group 12 680 false)⟩)
(.leaf ⟨245055,19,(.group 12 681 false)⟩)))
(.branch 245112
(.branch 245093
(.leaf ⟨245074,19,(.group 12 682 false)⟩)
(.leaf ⟨245093,19,(.group 12 683 false)⟩))
(.branch 245131
(.leaf ⟨245112,19,(.group 12 684 false)⟩)
(.leaf ⟨245131,19,(.group 12 685 false)⟩))))
(.branch 245226
(.branch 245188
(.branch 245169
(.leaf ⟨245150,19,(.group 12 686 false)⟩)
(.leaf ⟨245169,19,(.group 12 687 false)⟩))
(.branch 245207
(.leaf ⟨245188,19,(.group 12 688 false)⟩)
(.leaf ⟨245207,19,(.group 12 689 false)⟩)))
(.branch 245264
(.branch 245245
(.leaf ⟨245226,19,(.group 12 690 false)⟩)
(.leaf ⟨245245,19,(.group 12 691 false)⟩))
(.branch 245283
(.leaf ⟨245264,19,(.group 12 692 false)⟩)
(.leaf ⟨245283,19,(.group 12 693 false)⟩)))))
(.branch 245456
(.branch 245378
(.branch 245340
(.branch 245321
(.leaf ⟨245302,19,(.group 12 694 false)⟩)
(.leaf ⟨245321,19,(.group 12 695 false)⟩))
(.branch 245359
(.leaf ⟨245340,19,(.group 12 696 false)⟩)
(.leaf ⟨245359,19,(.group 12 697 false)⟩)))
(.branch 245416
(.branch 245397
(.leaf ⟨245378,19,(.group 12 698 false)⟩)
(.leaf ⟨245397,19,(.group 12 699 false)⟩))
(.branch 245436
(.leaf ⟨245416,20,(.group 12 700 false)⟩)
(.leaf ⟨245436,20,(.group 12 701 false)⟩))))
(.branch 245536
(.branch 245496
(.branch 245476
(.leaf ⟨245456,20,(.group 12 702 false)⟩)
(.leaf ⟨245476,20,(.group 12 703 false)⟩))
(.branch 245516
(.leaf ⟨245496,20,(.group 12 704 false)⟩)
(.leaf ⟨245516,20,(.group 12 705 false)⟩)))
(.branch 245576
(.branch 245556
(.leaf ⟨245536,20,(.group 12 706 false)⟩)
(.leaf ⟨245556,20,(.group 12 707 false)⟩))
(.branch 245596
(.leaf ⟨245576,20,(.group 12 708 false)⟩)
(.leaf ⟨245596,20,(.group 12 709 false)⟩)))))))

theorem tree228_checked : tree228.check 244390 245616 = true := by decide +kernel

def tree229 : Tree := (.branch 246256
(.branch 245936
(.branch 245776
(.branch 245696
(.branch 245656
(.branch 245636
(.leaf ⟨245616,20,(.group 12 710 false)⟩)
(.leaf ⟨245636,20,(.group 12 711 false)⟩))
(.branch 245676
(.leaf ⟨245656,20,(.group 12 712 false)⟩)
(.leaf ⟨245676,20,(.group 12 713 false)⟩)))
(.branch 245736
(.branch 245716
(.leaf ⟨245696,20,(.group 12 714 false)⟩)
(.leaf ⟨245716,20,(.group 12 715 false)⟩))
(.branch 245756
(.leaf ⟨245736,20,(.group 12 716 false)⟩)
(.leaf ⟨245756,20,(.group 12 717 false)⟩))))
(.branch 245856
(.branch 245816
(.branch 245796
(.leaf ⟨245776,20,(.group 12 718 false)⟩)
(.leaf ⟨245796,20,(.group 12 719 false)⟩))
(.branch 245836
(.leaf ⟨245816,20,(.group 12 720 false)⟩)
(.leaf ⟨245836,20,(.group 12 721 false)⟩)))
(.branch 245896
(.branch 245876
(.leaf ⟨245856,20,(.group 12 722 false)⟩)
(.leaf ⟨245876,20,(.group 12 723 false)⟩))
(.branch 245916
(.leaf ⟨245896,20,(.group 12 724 false)⟩)
(.leaf ⟨245916,20,(.group 12 725 false)⟩)))))
(.branch 246096
(.branch 246016
(.branch 245976
(.branch 245956
(.leaf ⟨245936,20,(.group 12 726 false)⟩)
(.leaf ⟨245956,20,(.group 12 727 false)⟩))
(.branch 245996
(.leaf ⟨245976,20,(.group 12 728 false)⟩)
(.leaf ⟨245996,20,(.group 12 729 false)⟩)))
(.branch 246056
(.branch 246036
(.leaf ⟨246016,20,(.group 12 730 false)⟩)
(.leaf ⟨246036,20,(.group 12 731 false)⟩))
(.branch 246076
(.leaf ⟨246056,20,(.group 12 732 false)⟩)
(.leaf ⟨246076,20,(.group 12 733 false)⟩))))
(.branch 246176
(.branch 246136
(.branch 246116
(.leaf ⟨246096,20,(.group 12 734 false)⟩)
(.leaf ⟨246116,20,(.group 12 735 false)⟩))
(.branch 246156
(.leaf ⟨246136,20,(.group 12 736 false)⟩)
(.leaf ⟨246156,20,(.group 12 737 false)⟩)))
(.branch 246216
(.branch 246196
(.leaf ⟨246176,20,(.group 12 738 false)⟩)
(.leaf ⟨246196,20,(.group 12 739 false)⟩))
(.branch 246236
(.leaf ⟨246216,20,(.group 12 740 false)⟩)
(.leaf ⟨246236,20,(.group 12 741 false)⟩))))))
(.branch 246576
(.branch 246416
(.branch 246336
(.branch 246296
(.branch 246276
(.leaf ⟨246256,20,(.group 12 742 false)⟩)
(.leaf ⟨246276,20,(.group 12 743 false)⟩))
(.branch 246316
(.leaf ⟨246296,20,(.group 12 744 false)⟩)
(.leaf ⟨246316,20,(.group 12 745 false)⟩)))
(.branch 246376
(.branch 246356
(.leaf ⟨246336,20,(.group 12 746 false)⟩)
(.leaf ⟨246356,20,(.group 12 747 false)⟩))
(.branch 246396
(.leaf ⟨246376,20,(.group 12 748 false)⟩)
(.leaf ⟨246396,20,(.group 12 749 false)⟩))))
(.branch 246496
(.branch 246456
(.branch 246436
(.leaf ⟨246416,20,(.group 12 750 false)⟩)
(.leaf ⟨246436,20,(.group 12 751 false)⟩))
(.branch 246476
(.leaf ⟨246456,20,(.group 12 752 false)⟩)
(.leaf ⟨246476,20,(.group 12 753 false)⟩)))
(.branch 246536
(.branch 246516
(.leaf ⟨246496,20,(.group 12 754 false)⟩)
(.leaf ⟨246516,20,(.group 12 755 false)⟩))
(.branch 246556
(.leaf ⟨246536,20,(.group 12 756 false)⟩)
(.leaf ⟨246556,20,(.group 12 757 false)⟩)))))
(.branch 246736
(.branch 246656
(.branch 246616
(.branch 246596
(.leaf ⟨246576,20,(.group 12 758 false)⟩)
(.leaf ⟨246596,20,(.group 12 759 false)⟩))
(.branch 246636
(.leaf ⟨246616,20,(.group 12 760 false)⟩)
(.leaf ⟨246636,20,(.group 12 761 false)⟩)))
(.branch 246696
(.branch 246676
(.leaf ⟨246656,20,(.group 12 762 false)⟩)
(.leaf ⟨246676,20,(.group 12 763 false)⟩))
(.branch 246716
(.leaf ⟨246696,20,(.group 12 764 false)⟩)
(.leaf ⟨246716,20,(.group 12 765 false)⟩))))
(.branch 246816
(.branch 246776
(.branch 246756
(.leaf ⟨246736,20,(.group 12 766 false)⟩)
(.leaf ⟨246756,20,(.group 12 767 false)⟩))
(.branch 246796
(.leaf ⟨246776,20,(.group 12 768 false)⟩)
(.leaf ⟨246796,20,(.group 12 769 false)⟩)))
(.branch 246856
(.branch 246836
(.leaf ⟨246816,20,(.group 12 770 false)⟩)
(.leaf ⟨246836,20,(.group 12 771 false)⟩))
(.branch 246876
(.leaf ⟨246856,20,(.group 12 772 false)⟩)
(.leaf ⟨246876,20,(.group 12 773 false)⟩)))))))

theorem tree229_checked : tree229.check 245616 246896 = true := by decide +kernel

def tree230 : Tree := (.branch 247536
(.branch 247216
(.branch 247056
(.branch 246976
(.branch 246936
(.branch 246916
(.leaf ⟨246896,20,(.group 12 774 false)⟩)
(.leaf ⟨246916,20,(.group 12 775 false)⟩))
(.branch 246956
(.leaf ⟨246936,20,(.group 12 776 false)⟩)
(.leaf ⟨246956,20,(.group 12 777 false)⟩)))
(.branch 247016
(.branch 246996
(.leaf ⟨246976,20,(.group 12 778 false)⟩)
(.leaf ⟨246996,20,(.group 12 779 false)⟩))
(.branch 247036
(.leaf ⟨247016,20,(.group 12 780 false)⟩)
(.leaf ⟨247036,20,(.group 12 781 false)⟩))))
(.branch 247136
(.branch 247096
(.branch 247076
(.leaf ⟨247056,20,(.group 12 782 false)⟩)
(.leaf ⟨247076,20,(.group 12 783 false)⟩))
(.branch 247116
(.leaf ⟨247096,20,(.group 12 784 false)⟩)
(.leaf ⟨247116,20,(.group 12 785 false)⟩)))
(.branch 247176
(.branch 247156
(.leaf ⟨247136,20,(.group 12 786 false)⟩)
(.leaf ⟨247156,20,(.group 12 787 false)⟩))
(.branch 247196
(.leaf ⟨247176,20,(.group 12 788 false)⟩)
(.leaf ⟨247196,20,(.group 12 789 false)⟩)))))
(.branch 247376
(.branch 247296
(.branch 247256
(.branch 247236
(.leaf ⟨247216,20,(.group 12 790 false)⟩)
(.leaf ⟨247236,20,(.group 12 791 false)⟩))
(.branch 247276
(.leaf ⟨247256,20,(.group 12 792 false)⟩)
(.leaf ⟨247276,20,(.group 12 793 false)⟩)))
(.branch 247336
(.branch 247316
(.leaf ⟨247296,20,(.group 12 794 false)⟩)
(.leaf ⟨247316,20,(.group 12 795 false)⟩))
(.branch 247356
(.leaf ⟨247336,20,(.group 12 796 false)⟩)
(.leaf ⟨247356,20,(.group 12 797 false)⟩))))
(.branch 247456
(.branch 247416
(.branch 247396
(.leaf ⟨247376,20,(.group 12 798 false)⟩)
(.leaf ⟨247396,20,(.group 12 799 false)⟩))
(.branch 247436
(.leaf ⟨247416,20,(.group 12 800 false)⟩)
(.leaf ⟨247436,20,(.group 12 801 false)⟩)))
(.branch 247496
(.branch 247476
(.leaf ⟨247456,20,(.group 12 802 false)⟩)
(.leaf ⟨247476,20,(.group 12 803 false)⟩))
(.branch 247516
(.leaf ⟨247496,20,(.group 12 804 false)⟩)
(.leaf ⟨247516,20,(.group 12 805 false)⟩))))))
(.branch 247859
(.branch 247696
(.branch 247616
(.branch 247576
(.branch 247556
(.leaf ⟨247536,20,(.group 12 806 false)⟩)
(.leaf ⟨247556,20,(.group 12 807 false)⟩))
(.branch 247596
(.leaf ⟨247576,20,(.group 12 808 false)⟩)
(.leaf ⟨247596,20,(.group 12 809 false)⟩)))
(.branch 247656
(.branch 247636
(.leaf ⟨247616,20,(.group 12 810 false)⟩)
(.leaf ⟨247636,20,(.group 12 811 false)⟩))
(.branch 247676
(.leaf ⟨247656,20,(.group 12 812 false)⟩)
(.leaf ⟨247676,20,(.group 12 813 false)⟩))))
(.branch 247776
(.branch 247736
(.branch 247716
(.leaf ⟨247696,20,(.group 12 814 false)⟩)
(.leaf ⟨247716,20,(.group 12 815 false)⟩))
(.branch 247756
(.leaf ⟨247736,20,(.group 12 816 false)⟩)
(.leaf ⟨247756,20,(.group 12 817 false)⟩)))
(.branch 247817
(.branch 247796
(.leaf ⟨247776,20,(.group 12 818 false)⟩)
(.leaf ⟨247796,21,(.group 12 819 false)⟩))
(.branch 247838
(.leaf ⟨247817,21,(.group 12 820 false)⟩)
(.leaf ⟨247838,21,(.group 12 821 false)⟩)))))
(.branch 248027
(.branch 247943
(.branch 247901
(.branch 247880
(.leaf ⟨247859,21,(.group 12 822 false)⟩)
(.leaf ⟨247880,21,(.group 12 823 false)⟩))
(.branch 247922
(.leaf ⟨247901,21,(.group 12 824 false)⟩)
(.leaf ⟨247922,21,(.group 12 825 false)⟩)))
(.branch 247985
(.branch 247964
(.leaf ⟨247943,21,(.group 12 826 false)⟩)
(.leaf ⟨247964,21,(.group 12 827 false)⟩))
(.branch 248006
(.leaf ⟨247985,21,(.group 12 828 false)⟩)
(.leaf ⟨248006,21,(.group 12 829 false)⟩))))
(.branch 248111
(.branch 248069
(.branch 248048
(.leaf ⟨248027,21,(.group 12 830 false)⟩)
(.leaf ⟨248048,21,(.group 12 831 false)⟩))
(.branch 248090
(.leaf ⟨248069,21,(.group 12 832 false)⟩)
(.leaf ⟨248090,21,(.group 12 833 false)⟩)))
(.branch 248153
(.branch 248132
(.leaf ⟨248111,21,(.group 12 834 false)⟩)
(.leaf ⟨248132,21,(.group 12 835 false)⟩))
(.branch 248174
(.leaf ⟨248153,21,(.group 12 836 false)⟩)
(.leaf ⟨248174,21,(.group 12 837 false)⟩)))))))

theorem tree230_checked : tree230.check 246896 248195 = true := by decide +kernel

def tree231 : Tree := (.branch 248867
(.branch 248531
(.branch 248363
(.branch 248279
(.branch 248237
(.branch 248216
(.leaf ⟨248195,21,(.group 12 838 false)⟩)
(.leaf ⟨248216,21,(.group 12 839 false)⟩))
(.branch 248258
(.leaf ⟨248237,21,(.group 12 840 false)⟩)
(.leaf ⟨248258,21,(.group 12 841 false)⟩)))
(.branch 248321
(.branch 248300
(.leaf ⟨248279,21,(.group 12 842 false)⟩)
(.leaf ⟨248300,21,(.group 12 843 false)⟩))
(.branch 248342
(.leaf ⟨248321,21,(.group 12 844 false)⟩)
(.leaf ⟨248342,21,(.group 12 845 false)⟩))))
(.branch 248447
(.branch 248405
(.branch 248384
(.leaf ⟨248363,21,(.group 12 846 false)⟩)
(.leaf ⟨248384,21,(.group 12 847 false)⟩))
(.branch 248426
(.leaf ⟨248405,21,(.group 12 848 false)⟩)
(.leaf ⟨248426,21,(.group 12 849 false)⟩)))
(.branch 248489
(.branch 248468
(.leaf ⟨248447,21,(.group 12 850 false)⟩)
(.leaf ⟨248468,21,(.group 12 851 false)⟩))
(.branch 248510
(.leaf ⟨248489,21,(.group 12 852 false)⟩)
(.leaf ⟨248510,21,(.group 12 853 false)⟩)))))
(.branch 248699
(.branch 248615
(.branch 248573
(.branch 248552
(.leaf ⟨248531,21,(.group 12 854 false)⟩)
(.leaf ⟨248552,21,(.group 12 855 false)⟩))
(.branch 248594
(.leaf ⟨248573,21,(.group 12 856 false)⟩)
(.leaf ⟨248594,21,(.group 12 857 false)⟩)))
(.branch 248657
(.branch 248636
(.leaf ⟨248615,21,(.group 12 858 false)⟩)
(.leaf ⟨248636,21,(.group 12 859 false)⟩))
(.branch 248678
(.leaf ⟨248657,21,(.group 12 860 false)⟩)
(.leaf ⟨248678,21,(.group 12 861 false)⟩))))
(.branch 248783
(.branch 248741
(.branch 248720
(.leaf ⟨248699,21,(.group 12 862 false)⟩)
(.leaf ⟨248720,21,(.group 12 863 false)⟩))
(.branch 248762
(.leaf ⟨248741,21,(.group 12 864 false)⟩)
(.leaf ⟨248762,21,(.group 12 865 false)⟩)))
(.branch 248825
(.branch 248804
(.leaf ⟨248783,21,(.group 12 866 false)⟩)
(.leaf ⟨248804,21,(.group 12 867 false)⟩))
(.branch 248846
(.leaf ⟨248825,21,(.group 12 868 false)⟩)
(.leaf ⟨248846,21,(.group 12 869 false)⟩))))))
(.branch 249203
(.branch 249035
(.branch 248951
(.branch 248909
(.branch 248888
(.leaf ⟨248867,21,(.group 12 870 false)⟩)
(.leaf ⟨248888,21,(.group 12 871 false)⟩))
(.branch 248930
(.leaf ⟨248909,21,(.group 12 872 false)⟩)
(.leaf ⟨248930,21,(.group 12 873 false)⟩)))
(.branch 248993
(.branch 248972
(.leaf ⟨248951,21,(.group 12 874 false)⟩)
(.leaf ⟨248972,21,(.group 12 875 false)⟩))
(.branch 249014
(.leaf ⟨248993,21,(.group 12 876 false)⟩)
(.leaf ⟨249014,21,(.group 12 877 false)⟩))))
(.branch 249119
(.branch 249077
(.branch 249056
(.leaf ⟨249035,21,(.group 12 878 false)⟩)
(.leaf ⟨249056,21,(.group 12 879 false)⟩))
(.branch 249098
(.leaf ⟨249077,21,(.group 12 880 false)⟩)
(.leaf ⟨249098,21,(.group 12 881 false)⟩)))
(.branch 249161
(.branch 249140
(.leaf ⟨249119,21,(.group 12 882 false)⟩)
(.leaf ⟨249140,21,(.group 12 883 false)⟩))
(.branch 249182
(.leaf ⟨249161,21,(.group 12 884 false)⟩)
(.leaf ⟨249182,21,(.group 12 885 false)⟩)))))
(.branch 249371
(.branch 249287
(.branch 249245
(.branch 249224
(.leaf ⟨249203,21,(.group 12 886 false)⟩)
(.leaf ⟨249224,21,(.group 12 887 false)⟩))
(.branch 249266
(.leaf ⟨249245,21,(.group 12 888 false)⟩)
(.leaf ⟨249266,21,(.group 12 889 false)⟩)))
(.branch 249329
(.branch 249308
(.leaf ⟨249287,21,(.group 12 890 false)⟩)
(.leaf ⟨249308,21,(.group 12 891 false)⟩))
(.branch 249350
(.leaf ⟨249329,21,(.group 12 892 false)⟩)
(.leaf ⟨249350,21,(.group 12 893 false)⟩))))
(.branch 249455
(.branch 249413
(.branch 249392
(.leaf ⟨249371,21,(.group 12 894 false)⟩)
(.leaf ⟨249392,21,(.group 12 895 false)⟩))
(.branch 249434
(.leaf ⟨249413,21,(.group 12 896 false)⟩)
(.leaf ⟨249434,21,(.group 12 897 false)⟩)))
(.branch 249497
(.branch 249476
(.leaf ⟨249455,21,(.group 12 898 false)⟩)
(.leaf ⟨249476,21,(.group 12 899 false)⟩))
(.branch 249518
(.leaf ⟨249497,21,(.group 12 900 false)⟩)
(.leaf ⟨249518,21,(.group 12 901 false)⟩)))))))

theorem tree231_checked : tree231.check 248195 249539 = true := by decide +kernel

def tree232 : Tree := (.branch 250211
(.branch 249875
(.branch 249707
(.branch 249623
(.branch 249581
(.branch 249560
(.leaf ⟨249539,21,(.group 12 902 false)⟩)
(.leaf ⟨249560,21,(.group 12 903 false)⟩))
(.branch 249602
(.leaf ⟨249581,21,(.group 12 904 false)⟩)
(.leaf ⟨249602,21,(.group 12 905 false)⟩)))
(.branch 249665
(.branch 249644
(.leaf ⟨249623,21,(.group 12 906 false)⟩)
(.leaf ⟨249644,21,(.group 12 907 false)⟩))
(.branch 249686
(.leaf ⟨249665,21,(.group 12 908 false)⟩)
(.leaf ⟨249686,21,(.group 12 909 false)⟩))))
(.branch 249791
(.branch 249749
(.branch 249728
(.leaf ⟨249707,21,(.group 12 910 false)⟩)
(.leaf ⟨249728,21,(.group 12 911 false)⟩))
(.branch 249770
(.leaf ⟨249749,21,(.group 12 912 false)⟩)
(.leaf ⟨249770,21,(.group 12 913 false)⟩)))
(.branch 249833
(.branch 249812
(.leaf ⟨249791,21,(.group 12 914 false)⟩)
(.leaf ⟨249812,21,(.group 12 915 false)⟩))
(.branch 249854
(.leaf ⟨249833,21,(.group 12 916 false)⟩)
(.leaf ⟨249854,21,(.group 12 917 false)⟩)))))
(.branch 250043
(.branch 249959
(.branch 249917
(.branch 249896
(.leaf ⟨249875,21,(.group 12 918 false)⟩)
(.leaf ⟨249896,21,(.group 12 919 false)⟩))
(.branch 249938
(.leaf ⟨249917,21,(.group 12 920 false)⟩)
(.leaf ⟨249938,21,(.group 12 921 false)⟩)))
(.branch 250001
(.branch 249980
(.leaf ⟨249959,21,(.group 12 922 false)⟩)
(.leaf ⟨249980,21,(.group 12 923 false)⟩))
(.branch 250022
(.leaf ⟨250001,21,(.group 12 924 false)⟩)
(.leaf ⟨250022,21,(.group 12 925 false)⟩))))
(.branch 250127
(.branch 250085
(.branch 250064
(.leaf ⟨250043,21,(.group 12 926 false)⟩)
(.leaf ⟨250064,21,(.group 12 927 false)⟩))
(.branch 250106
(.leaf ⟨250085,21,(.group 12 928 false)⟩)
(.leaf ⟨250106,21,(.group 12 929 false)⟩)))
(.branch 250169
(.branch 250148
(.leaf ⟨250127,21,(.group 12 930 false)⟩)
(.leaf ⟨250148,21,(.group 12 931 false)⟩))
(.branch 250190
(.leaf ⟨250169,21,(.group 12 932 false)⟩)
(.leaf ⟨250190,21,(.group 12 933 false)⟩))))))
(.branch 250547
(.branch 250379
(.branch 250295
(.branch 250253
(.branch 250232
(.leaf ⟨250211,21,(.group 12 934 false)⟩)
(.leaf ⟨250232,21,(.group 12 935 false)⟩))
(.branch 250274
(.leaf ⟨250253,21,(.group 12 936 false)⟩)
(.leaf ⟨250274,21,(.group 12 937 false)⟩)))
(.branch 250337
(.branch 250316
(.leaf ⟨250295,21,(.group 12 938 false)⟩)
(.leaf ⟨250316,21,(.group 12 939 false)⟩))
(.branch 250358
(.leaf ⟨250337,21,(.group 12 940 false)⟩)
(.leaf ⟨250358,21,(.group 12 941 false)⟩))))
(.branch 250463
(.branch 250421
(.branch 250400
(.leaf ⟨250379,21,(.group 12 942 false)⟩)
(.leaf ⟨250400,21,(.group 12 943 false)⟩))
(.branch 250442
(.leaf ⟨250421,21,(.group 12 944 false)⟩)
(.leaf ⟨250442,21,(.group 12 945 false)⟩)))
(.branch 250505
(.branch 250484
(.leaf ⟨250463,21,(.group 12 946 false)⟩)
(.leaf ⟨250484,21,(.group 12 947 false)⟩))
(.branch 250526
(.leaf ⟨250505,21,(.group 12 948 false)⟩)
(.leaf ⟨250526,21,(.group 12 949 false)⟩)))))
(.branch 250719
(.branch 250631
(.branch 250589
(.branch 250568
(.leaf ⟨250547,21,(.group 12 950 false)⟩)
(.leaf ⟨250568,21,(.group 12 951 false)⟩))
(.branch 250610
(.leaf ⟨250589,21,(.group 12 952 false)⟩)
(.leaf ⟨250610,21,(.group 12 953 false)⟩)))
(.branch 250675
(.branch 250653
(.leaf ⟨250631,22,(.group 12 954 false)⟩)
(.leaf ⟨250653,22,(.group 12 955 false)⟩))
(.branch 250697
(.leaf ⟨250675,22,(.group 12 956 false)⟩)
(.leaf ⟨250697,22,(.group 12 957 false)⟩))))
(.branch 250807
(.branch 250763
(.branch 250741
(.leaf ⟨250719,22,(.group 12 958 false)⟩)
(.leaf ⟨250741,22,(.group 12 959 false)⟩))
(.branch 250785
(.leaf ⟨250763,22,(.group 12 960 false)⟩)
(.leaf ⟨250785,22,(.group 12 961 false)⟩)))
(.branch 250851
(.branch 250829
(.leaf ⟨250807,22,(.group 12 962 false)⟩)
(.leaf ⟨250829,22,(.group 12 963 false)⟩))
(.branch 250873
(.leaf ⟨250851,22,(.group 12 964 false)⟩)
(.leaf ⟨250873,22,(.group 12 965 false)⟩)))))))

theorem tree232_checked : tree232.check 249539 250895 = true := by decide +kernel

def tree233 : Tree := (.branch 251599
(.branch 251247
(.branch 251071
(.branch 250983
(.branch 250939
(.branch 250917
(.leaf ⟨250895,22,(.group 12 966 false)⟩)
(.leaf ⟨250917,22,(.group 12 967 false)⟩))
(.branch 250961
(.leaf ⟨250939,22,(.group 12 968 false)⟩)
(.leaf ⟨250961,22,(.group 12 969 false)⟩)))
(.branch 251027
(.branch 251005
(.leaf ⟨250983,22,(.group 12 970 false)⟩)
(.leaf ⟨251005,22,(.group 12 971 false)⟩))
(.branch 251049
(.leaf ⟨251027,22,(.group 12 972 false)⟩)
(.leaf ⟨251049,22,(.group 12 973 false)⟩))))
(.branch 251159
(.branch 251115
(.branch 251093
(.leaf ⟨251071,22,(.group 12 974 false)⟩)
(.leaf ⟨251093,22,(.group 12 975 false)⟩))
(.branch 251137
(.leaf ⟨251115,22,(.group 12 976 false)⟩)
(.leaf ⟨251137,22,(.group 12 977 false)⟩)))
(.branch 251203
(.branch 251181
(.leaf ⟨251159,22,(.group 12 978 false)⟩)
(.leaf ⟨251181,22,(.group 12 979 false)⟩))
(.branch 251225
(.leaf ⟨251203,22,(.group 12 980 false)⟩)
(.leaf ⟨251225,22,(.group 12 981 false)⟩)))))
(.branch 251423
(.branch 251335
(.branch 251291
(.branch 251269
(.leaf ⟨251247,22,(.group 12 982 false)⟩)
(.leaf ⟨251269,22,(.group 12 983 false)⟩))
(.branch 251313
(.leaf ⟨251291,22,(.group 12 984 false)⟩)
(.leaf ⟨251313,22,(.group 12 985 false)⟩)))
(.branch 251379
(.branch 251357
(.leaf ⟨251335,22,(.group 12 986 false)⟩)
(.leaf ⟨251357,22,(.group 12 987 false)⟩))
(.branch 251401
(.leaf ⟨251379,22,(.group 12 988 false)⟩)
(.leaf ⟨251401,22,(.group 12 989 false)⟩))))
(.branch 251511
(.branch 251467
(.branch 251445
(.leaf ⟨251423,22,(.group 12 990 false)⟩)
(.leaf ⟨251445,22,(.group 12 991 false)⟩))
(.branch 251489
(.leaf ⟨251467,22,(.group 12 992 false)⟩)
(.leaf ⟨251489,22,(.group 12 993 false)⟩)))
(.branch 251555
(.branch 251533
(.leaf ⟨251511,22,(.group 12 994 false)⟩)
(.leaf ⟨251533,22,(.group 12 995 false)⟩))
(.branch 251577
(.leaf ⟨251555,22,(.group 12 996 false)⟩)
(.leaf ⟨251577,22,(.group 12 997 false)⟩))))))
(.branch 251951
(.branch 251775
(.branch 251687
(.branch 251643
(.branch 251621
(.leaf ⟨251599,22,(.group 12 998 false)⟩)
(.leaf ⟨251621,22,(.group 12 999 false)⟩))
(.branch 251665
(.leaf ⟨251643,22,(.group 12 1000 false)⟩)
(.leaf ⟨251665,22,(.group 12 1001 false)⟩)))
(.branch 251731
(.branch 251709
(.leaf ⟨251687,22,(.group 12 1002 false)⟩)
(.leaf ⟨251709,22,(.group 12 1003 false)⟩))
(.branch 251753
(.leaf ⟨251731,22,(.group 12 1004 false)⟩)
(.leaf ⟨251753,22,(.group 12 1005 false)⟩))))
(.branch 251863
(.branch 251819
(.branch 251797
(.leaf ⟨251775,22,(.group 12 1006 false)⟩)
(.leaf ⟨251797,22,(.group 12 1007 false)⟩))
(.branch 251841
(.leaf ⟨251819,22,(.group 12 1008 false)⟩)
(.leaf ⟨251841,22,(.group 12 1009 false)⟩)))
(.branch 251907
(.branch 251885
(.leaf ⟨251863,22,(.group 12 1010 false)⟩)
(.leaf ⟨251885,22,(.group 12 1011 false)⟩))
(.branch 251929
(.leaf ⟨251907,22,(.group 12 1012 false)⟩)
(.leaf ⟨251929,22,(.group 12 1013 false)⟩)))))
(.branch 252127
(.branch 252039
(.branch 251995
(.branch 251973
(.leaf ⟨251951,22,(.group 12 1014 false)⟩)
(.leaf ⟨251973,22,(.group 12 1015 false)⟩))
(.branch 252017
(.leaf ⟨251995,22,(.group 12 1016 false)⟩)
(.leaf ⟨252017,22,(.group 12 1017 false)⟩)))
(.branch 252083
(.branch 252061
(.leaf ⟨252039,22,(.group 12 1018 false)⟩)
(.leaf ⟨252061,22,(.group 12 1019 false)⟩))
(.branch 252105
(.leaf ⟨252083,22,(.group 12 1020 false)⟩)
(.leaf ⟨252105,22,(.group 12 1021 false)⟩))))
(.branch 252203
(.branch 252171
(.branch 252149
(.leaf ⟨252127,22,(.group 12 1022 false)⟩)
(.leaf ⟨252149,22,(.group 12 1023 false)⟩))
(.branch 252187
(.leaf ⟨252171,16,(.group 1 148 true)⟩)
(.leaf ⟨252187,16,(.group 1 149 true)⟩)))
(.branch 252235
(.branch 252219
(.leaf ⟨252203,16,(.group 1 150 true)⟩)
(.leaf ⟨252219,16,(.group 1 151 true)⟩))
(.branch 252251
(.leaf ⟨252235,16,(.group 1 152 true)⟩)
(.leaf ⟨252251,16,(.group 1 153 true)⟩)))))))

theorem tree233_checked : tree233.check 250895 252267 = true := by decide +kernel

def tree234 : Tree := (.branch 252800
(.branch 252528
(.branch 252395
(.branch 252331
(.branch 252299
(.branch 252283
(.leaf ⟨252267,16,(.group 1 154 true)⟩)
(.leaf ⟨252283,16,(.group 1 155 true)⟩))
(.branch 252315
(.leaf ⟨252299,16,(.group 1 156 true)⟩)
(.leaf ⟨252315,16,(.group 1 157 true)⟩)))
(.branch 252363
(.branch 252347
(.leaf ⟨252331,16,(.group 1 158 true)⟩)
(.leaf ⟨252347,16,(.group 1 159 true)⟩))
(.branch 252379
(.leaf ⟨252363,16,(.group 1 160 true)⟩)
(.leaf ⟨252379,16,(.group 1 161 true)⟩))))
(.branch 252460
(.branch 252427
(.branch 252411
(.leaf ⟨252395,16,(.group 1 162 true)⟩)
(.leaf ⟨252411,16,(.group 1 163 true)⟩))
(.branch 252443
(.leaf ⟨252427,16,(.group 1 164 true)⟩)
(.leaf ⟨252443,17,(.group 1 165 true)⟩)))
(.branch 252494
(.branch 252477
(.leaf ⟨252460,17,(.group 1 166 true)⟩)
(.leaf ⟨252477,17,(.group 1 167 true)⟩))
(.branch 252511
(.leaf ⟨252494,17,(.group 1 168 true)⟩)
(.leaf ⟨252511,17,(.group 1 169 true)⟩)))))
(.branch 252664
(.branch 252596
(.branch 252562
(.branch 252545
(.leaf ⟨252528,17,(.group 1 170 true)⟩)
(.leaf ⟨252545,17,(.group 1 171 true)⟩))
(.branch 252579
(.leaf ⟨252562,17,(.group 1 172 true)⟩)
(.leaf ⟨252579,17,(.group 1 173 true)⟩)))
(.branch 252630
(.branch 252613
(.leaf ⟨252596,17,(.group 1 174 true)⟩)
(.leaf ⟨252613,17,(.group 1 175 true)⟩))
(.branch 252647
(.leaf ⟨252630,17,(.group 1 176 true)⟩)
(.leaf ⟨252647,17,(.group 1 177 true)⟩))))
(.branch 252732
(.branch 252698
(.branch 252681
(.leaf ⟨252664,17,(.group 1 178 true)⟩)
(.leaf ⟨252681,17,(.group 1 179 true)⟩))
(.branch 252715
(.leaf ⟨252698,17,(.group 1 180 true)⟩)
(.leaf ⟨252715,17,(.group 1 181 true)⟩)))
(.branch 252766
(.branch 252749
(.leaf ⟨252732,17,(.group 1 182 true)⟩)
(.leaf ⟨252749,17,(.group 1 183 true)⟩))
(.branch 252783
(.leaf ⟨252766,17,(.group 1 184 true)⟩)
(.leaf ⟨252783,17,(.group 1 185 true)⟩))))))
(.branch 253072
(.branch 252936
(.branch 252868
(.branch 252834
(.branch 252817
(.leaf ⟨252800,17,(.group 1 186 true)⟩)
(.leaf ⟨252817,17,(.group 1 187 true)⟩))
(.branch 252851
(.leaf ⟨252834,17,(.group 1 188 true)⟩)
(.leaf ⟨252851,17,(.group 1 189 true)⟩)))
(.branch 252902
(.branch 252885
(.leaf ⟨252868,17,(.group 1 190 true)⟩)
(.leaf ⟨252885,17,(.group 1 191 true)⟩))
(.branch 252919
(.leaf ⟨252902,17,(.group 1 192 true)⟩)
(.leaf ⟨252919,17,(.group 1 193 true)⟩))))
(.branch 253004
(.branch 252970
(.branch 252953
(.leaf ⟨252936,17,(.group 1 194 true)⟩)
(.leaf ⟨252953,17,(.group 1 195 true)⟩))
(.branch 252987
(.leaf ⟨252970,17,(.group 1 196 true)⟩)
(.leaf ⟨252987,17,(.group 1 197 true)⟩)))
(.branch 253038
(.branch 253021
(.leaf ⟨253004,17,(.group 1 198 true)⟩)
(.leaf ⟨253021,17,(.group 1 199 true)⟩))
(.branch 253055
(.leaf ⟨253038,17,(.group 1 200 true)⟩)
(.leaf ⟨253055,17,(.group 1 201 true)⟩)))))
(.branch 253208
(.branch 253140
(.branch 253106
(.branch 253089
(.leaf ⟨253072,17,(.group 1 202 true)⟩)
(.leaf ⟨253089,17,(.group 1 203 true)⟩))
(.branch 253123
(.leaf ⟨253106,17,(.group 1 204 true)⟩)
(.leaf ⟨253123,17,(.group 1 205 true)⟩)))
(.branch 253174
(.branch 253157
(.leaf ⟨253140,17,(.group 1 206 true)⟩)
(.leaf ⟨253157,17,(.group 1 207 true)⟩))
(.branch 253191
(.leaf ⟨253174,17,(.group 1 208 true)⟩)
(.leaf ⟨253191,17,(.group 1 209 true)⟩))))
(.branch 253276
(.branch 253242
(.branch 253225
(.leaf ⟨253208,17,(.group 1 210 true)⟩)
(.leaf ⟨253225,17,(.group 1 211 true)⟩))
(.branch 253259
(.leaf ⟨253242,17,(.group 1 212 true)⟩)
(.leaf ⟨253259,17,(.group 1 213 true)⟩)))
(.branch 253310
(.branch 253293
(.leaf ⟨253276,17,(.group 1 214 true)⟩)
(.leaf ⟨253293,17,(.group 1 215 true)⟩))
(.branch 253327
(.leaf ⟨253310,17,(.group 1 216 true)⟩)
(.leaf ⟨253327,17,(.group 1 217 true)⟩)))))))

theorem tree234_checked : tree234.check 252267 253344 = true := by decide +kernel

def tree235 : Tree := (.branch 253918
(.branch 253630
(.branch 253486
(.branch 253414
(.branch 253378
(.branch 253361
(.leaf ⟨253344,17,(.group 1 218 true)⟩)
(.leaf ⟨253361,17,(.group 1 219 true)⟩))
(.branch 253396
(.leaf ⟨253378,18,(.group 1 220 true)⟩)
(.leaf ⟨253396,18,(.group 1 221 true)⟩)))
(.branch 253450
(.branch 253432
(.leaf ⟨253414,18,(.group 1 222 true)⟩)
(.leaf ⟨253432,18,(.group 1 223 true)⟩))
(.branch 253468
(.leaf ⟨253450,18,(.group 1 224 true)⟩)
(.leaf ⟨253468,18,(.group 1 225 true)⟩))))
(.branch 253558
(.branch 253522
(.branch 253504
(.leaf ⟨253486,18,(.group 1 226 true)⟩)
(.leaf ⟨253504,18,(.group 1 227 true)⟩))
(.branch 253540
(.leaf ⟨253522,18,(.group 1 228 true)⟩)
(.leaf ⟨253540,18,(.group 1 229 true)⟩)))
(.branch 253594
(.branch 253576
(.leaf ⟨253558,18,(.group 1 230 true)⟩)
(.leaf ⟨253576,18,(.group 1 231 true)⟩))
(.branch 253612
(.leaf ⟨253594,18,(.group 1 232 true)⟩)
(.leaf ⟨253612,18,(.group 1 233 true)⟩)))))
(.branch 253774
(.branch 253702
(.branch 253666
(.branch 253648
(.leaf ⟨253630,18,(.group 1 234 true)⟩)
(.leaf ⟨253648,18,(.group 1 235 true)⟩))
(.branch 253684
(.leaf ⟨253666,18,(.group 1 236 true)⟩)
(.leaf ⟨253684,18,(.group 1 237 true)⟩)))
(.branch 253738
(.branch 253720
(.leaf ⟨253702,18,(.group 1 238 true)⟩)
(.leaf ⟨253720,18,(.group 1 239 true)⟩))
(.branch 253756
(.leaf ⟨253738,18,(.group 1 240 true)⟩)
(.leaf ⟨253756,18,(.group 1 241 true)⟩))))
(.branch 253846
(.branch 253810
(.branch 253792
(.leaf ⟨253774,18,(.group 1 242 true)⟩)
(.leaf ⟨253792,18,(.group 1 243 true)⟩))
(.branch 253828
(.leaf ⟨253810,18,(.group 1 244 true)⟩)
(.leaf ⟨253828,18,(.group 1 245 true)⟩)))
(.branch 253882
(.branch 253864
(.leaf ⟨253846,18,(.group 1 246 true)⟩)
(.leaf ⟨253864,18,(.group 1 247 true)⟩))
(.branch 253900
(.leaf ⟨253882,18,(.group 1 248 true)⟩)
(.leaf ⟨253900,18,(.group 1 249 true)⟩))))))
(.branch 254206
(.branch 254062
(.branch 253990
(.branch 253954
(.branch 253936
(.leaf ⟨253918,18,(.group 1 250 true)⟩)
(.leaf ⟨253936,18,(.group 1 251 true)⟩))
(.branch 253972
(.leaf ⟨253954,18,(.group 1 252 true)⟩)
(.leaf ⟨253972,18,(.group 1 253 true)⟩)))
(.branch 254026
(.branch 254008
(.leaf ⟨253990,18,(.group 1 254 true)⟩)
(.leaf ⟨254008,18,(.group 1 255 true)⟩))
(.branch 254044
(.leaf ⟨254026,18,(.group 1 256 true)⟩)
(.leaf ⟨254044,18,(.group 1 257 true)⟩))))
(.branch 254134
(.branch 254098
(.branch 254080
(.leaf ⟨254062,18,(.group 1 258 true)⟩)
(.leaf ⟨254080,18,(.group 1 259 true)⟩))
(.branch 254116
(.leaf ⟨254098,18,(.group 1 260 true)⟩)
(.leaf ⟨254116,18,(.group 1 261 true)⟩)))
(.branch 254170
(.branch 254152
(.leaf ⟨254134,18,(.group 1 262 true)⟩)
(.leaf ⟨254152,18,(.group 1 263 true)⟩))
(.branch 254188
(.leaf ⟨254170,18,(.group 1 264 true)⟩)
(.leaf ⟨254188,18,(.group 1 265 true)⟩)))))
(.branch 254350
(.branch 254278
(.branch 254242
(.branch 254224
(.leaf ⟨254206,18,(.group 1 266 true)⟩)
(.leaf ⟨254224,18,(.group 1 267 true)⟩))
(.branch 254260
(.leaf ⟨254242,18,(.group 1 268 true)⟩)
(.leaf ⟨254260,18,(.group 1 269 true)⟩)))
(.branch 254314
(.branch 254296
(.leaf ⟨254278,18,(.group 1 270 true)⟩)
(.leaf ⟨254296,18,(.group 1 271 true)⟩))
(.branch 254332
(.leaf ⟨254314,18,(.group 1 272 true)⟩)
(.leaf ⟨254332,18,(.group 1 273 true)⟩))))
(.branch 254422
(.branch 254386
(.branch 254368
(.leaf ⟨254350,18,(.group 1 274 true)⟩)
(.leaf ⟨254368,18,(.group 1 275 true)⟩))
(.branch 254404
(.leaf ⟨254386,18,(.group 1 276 true)⟩)
(.leaf ⟨254404,18,(.group 1 277 true)⟩)))
(.branch 254458
(.branch 254440
(.leaf ⟨254422,18,(.group 1 278 true)⟩)
(.leaf ⟨254440,18,(.group 1 279 true)⟩))
(.branch 254476
(.leaf ⟨254458,18,(.group 1 280 true)⟩)
(.leaf ⟨254476,18,(.group 1 281 true)⟩)))))))

theorem tree235_checked : tree235.check 253344 254494 = true := by decide +kernel

def tree236 : Tree := (.branch 255098
(.branch 254794
(.branch 254642
(.branch 254566
(.branch 254530
(.branch 254512
(.leaf ⟨254494,18,(.group 1 282 true)⟩)
(.leaf ⟨254512,18,(.group 1 283 true)⟩))
(.branch 254548
(.leaf ⟨254530,18,(.group 1 284 true)⟩)
(.leaf ⟨254548,18,(.group 1 285 true)⟩)))
(.branch 254604
(.branch 254585
(.leaf ⟨254566,19,(.group 1 286 true)⟩)
(.leaf ⟨254585,19,(.group 1 287 true)⟩))
(.branch 254623
(.leaf ⟨254604,19,(.group 1 288 true)⟩)
(.leaf ⟨254623,19,(.group 1 289 true)⟩))))
(.branch 254718
(.branch 254680
(.branch 254661
(.leaf ⟨254642,19,(.group 1 290 true)⟩)
(.leaf ⟨254661,19,(.group 1 291 true)⟩))
(.branch 254699
(.leaf ⟨254680,19,(.group 1 292 true)⟩)
(.leaf ⟨254699,19,(.group 1 293 true)⟩)))
(.branch 254756
(.branch 254737
(.leaf ⟨254718,19,(.group 1 294 true)⟩)
(.leaf ⟨254737,19,(.group 1 295 true)⟩))
(.branch 254775
(.leaf ⟨254756,19,(.group 1 296 true)⟩)
(.leaf ⟨254775,19,(.group 1 297 true)⟩)))))
(.branch 254946
(.branch 254870
(.branch 254832
(.branch 254813
(.leaf ⟨254794,19,(.group 1 298 true)⟩)
(.leaf ⟨254813,19,(.group 1 299 true)⟩))
(.branch 254851
(.leaf ⟨254832,19,(.group 1 300 true)⟩)
(.leaf ⟨254851,19,(.group 1 301 true)⟩)))
(.branch 254908
(.branch 254889
(.leaf ⟨254870,19,(.group 1 302 true)⟩)
(.leaf ⟨254889,19,(.group 1 303 true)⟩))
(.branch 254927
(.leaf ⟨254908,19,(.group 1 304 true)⟩)
(.leaf ⟨254927,19,(.group 1 305 true)⟩))))
(.branch 255022
(.branch 254984
(.branch 254965
(.leaf ⟨254946,19,(.group 1 306 true)⟩)
(.leaf ⟨254965,19,(.group 1 307 true)⟩))
(.branch 255003
(.leaf ⟨254984,19,(.group 1 308 true)⟩)
(.leaf ⟨255003,19,(.group 1 309 true)⟩)))
(.branch 255060
(.branch 255041
(.leaf ⟨255022,19,(.group 1 310 true)⟩)
(.leaf ⟨255041,19,(.group 1 311 true)⟩))
(.branch 255079
(.leaf ⟨255060,19,(.group 1 312 true)⟩)
(.leaf ⟨255079,19,(.group 1 313 true)⟩))))))
(.branch 255402
(.branch 255250
(.branch 255174
(.branch 255136
(.branch 255117
(.leaf ⟨255098,19,(.group 1 314 true)⟩)
(.leaf ⟨255117,19,(.group 1 315 true)⟩))
(.branch 255155
(.leaf ⟨255136,19,(.group 1 316 true)⟩)
(.leaf ⟨255155,19,(.group 1 317 true)⟩)))
(.branch 255212
(.branch 255193
(.leaf ⟨255174,19,(.group 1 318 true)⟩)
(.leaf ⟨255193,19,(.group 1 319 true)⟩))
(.branch 255231
(.leaf ⟨255212,19,(.group 1 320 true)⟩)
(.leaf ⟨255231,19,(.group 1 321 true)⟩))))
(.branch 255326
(.branch 255288
(.branch 255269
(.leaf ⟨255250,19,(.group 1 322 true)⟩)
(.leaf ⟨255269,19,(.group 1 323 true)⟩))
(.branch 255307
(.leaf ⟨255288,19,(.group 1 324 true)⟩)
(.leaf ⟨255307,19,(.group 1 325 true)⟩)))
(.branch 255364
(.branch 255345
(.leaf ⟨255326,19,(.group 1 326 true)⟩)
(.leaf ⟨255345,19,(.group 1 327 true)⟩))
(.branch 255383
(.leaf ⟨255364,19,(.group 1 328 true)⟩)
(.leaf ⟨255383,19,(.group 1 329 true)⟩)))))
(.branch 255554
(.branch 255478
(.branch 255440
(.branch 255421
(.leaf ⟨255402,19,(.group 1 330 true)⟩)
(.leaf ⟨255421,19,(.group 1 331 true)⟩))
(.branch 255459
(.leaf ⟨255440,19,(.group 1 332 true)⟩)
(.leaf ⟨255459,19,(.group 1 333 true)⟩)))
(.branch 255516
(.branch 255497
(.leaf ⟨255478,19,(.group 1 334 true)⟩)
(.leaf ⟨255497,19,(.group 1 335 true)⟩))
(.branch 255535
(.leaf ⟨255516,19,(.group 1 336 true)⟩)
(.leaf ⟨255535,19,(.group 1 337 true)⟩))))
(.branch 255630
(.branch 255592
(.branch 255573
(.leaf ⟨255554,19,(.group 1 338 true)⟩)
(.leaf ⟨255573,19,(.group 1 339 true)⟩))
(.branch 255611
(.leaf ⟨255592,19,(.group 1 340 true)⟩)
(.leaf ⟨255611,19,(.group 1 341 true)⟩)))
(.branch 255668
(.branch 255649
(.leaf ⟨255630,19,(.group 1 342 true)⟩)
(.leaf ⟨255649,19,(.group 1 343 true)⟩))
(.branch 255687
(.leaf ⟨255668,19,(.group 1 344 true)⟩)
(.leaf ⟨255687,19,(.group 1 345 true)⟩)))))))

theorem tree236_checked : tree236.check 254494 255706 = true := by decide +kernel

def tree237 : Tree := (.branch 256328
(.branch 256010
(.branch 255858
(.branch 255782
(.branch 255744
(.branch 255725
(.leaf ⟨255706,19,(.group 1 346 true)⟩)
(.leaf ⟨255725,19,(.group 1 347 true)⟩))
(.branch 255763
(.leaf ⟨255744,19,(.group 1 348 true)⟩)
(.leaf ⟨255763,19,(.group 1 349 true)⟩)))
(.branch 255820
(.branch 255801
(.leaf ⟨255782,19,(.group 1 350 true)⟩)
(.leaf ⟨255801,19,(.group 1 351 true)⟩))
(.branch 255839
(.leaf ⟨255820,19,(.group 1 352 true)⟩)
(.leaf ⟨255839,19,(.group 1 353 true)⟩))))
(.branch 255934
(.branch 255896
(.branch 255877
(.leaf ⟨255858,19,(.group 1 354 true)⟩)
(.leaf ⟨255877,19,(.group 1 355 true)⟩))
(.branch 255915
(.leaf ⟨255896,19,(.group 1 356 true)⟩)
(.leaf ⟨255915,19,(.group 1 357 true)⟩)))
(.branch 255972
(.branch 255953
(.leaf ⟨255934,19,(.group 1 358 true)⟩)
(.leaf ⟨255953,19,(.group 1 359 true)⟩))
(.branch 255991
(.leaf ⟨255972,19,(.group 1 360 true)⟩)
(.leaf ⟨255991,19,(.group 1 361 true)⟩)))))
(.branch 256168
(.branch 256088
(.branch 256048
(.branch 256029
(.leaf ⟨256010,19,(.group 1 362 true)⟩)
(.leaf ⟨256029,19,(.group 1 363 true)⟩))
(.branch 256068
(.leaf ⟨256048,20,(.group 1 364 true)⟩)
(.leaf ⟨256068,20,(.group 1 365 true)⟩)))
(.branch 256128
(.branch 256108
(.leaf ⟨256088,20,(.group 1 366 true)⟩)
(.leaf ⟨256108,20,(.group 1 367 true)⟩))
(.branch 256148
(.leaf ⟨256128,20,(.group 1 368 true)⟩)
(.leaf ⟨256148,20,(.group 1 369 true)⟩))))
(.branch 256248
(.branch 256208
(.branch 256188
(.leaf ⟨256168,20,(.group 1 370 true)⟩)
(.leaf ⟨256188,20,(.group 1 371 true)⟩))
(.branch 256228
(.leaf ⟨256208,20,(.group 1 372 true)⟩)
(.leaf ⟨256228,20,(.group 1 373 true)⟩)))
(.branch 256288
(.branch 256268
(.leaf ⟨256248,20,(.group 1 374 true)⟩)
(.leaf ⟨256268,20,(.group 1 375 true)⟩))
(.branch 256308
(.leaf ⟨256288,20,(.group 1 376 true)⟩)
(.leaf ⟨256308,20,(.group 1 377 true)⟩))))))
(.branch 256648
(.branch 256488
(.branch 256408
(.branch 256368
(.branch 256348
(.leaf ⟨256328,20,(.group 1 378 true)⟩)
(.leaf ⟨256348,20,(.group 1 379 true)⟩))
(.branch 256388
(.leaf ⟨256368,20,(.group 1 380 true)⟩)
(.leaf ⟨256388,20,(.group 1 381 true)⟩)))
(.branch 256448
(.branch 256428
(.leaf ⟨256408,20,(.group 1 382 true)⟩)
(.leaf ⟨256428,20,(.group 1 383 true)⟩))
(.branch 256468
(.leaf ⟨256448,20,(.group 1 384 true)⟩)
(.leaf ⟨256468,20,(.group 1 385 true)⟩))))
(.branch 256568
(.branch 256528
(.branch 256508
(.leaf ⟨256488,20,(.group 1 386 true)⟩)
(.leaf ⟨256508,20,(.group 1 387 true)⟩))
(.branch 256548
(.leaf ⟨256528,20,(.group 1 388 true)⟩)
(.leaf ⟨256548,20,(.group 1 389 true)⟩)))
(.branch 256608
(.branch 256588
(.leaf ⟨256568,20,(.group 1 390 true)⟩)
(.leaf ⟨256588,20,(.group 1 391 true)⟩))
(.branch 256628
(.leaf ⟨256608,20,(.group 1 392 true)⟩)
(.leaf ⟨256628,20,(.group 1 393 true)⟩)))))
(.branch 256808
(.branch 256728
(.branch 256688
(.branch 256668
(.leaf ⟨256648,20,(.group 1 394 true)⟩)
(.leaf ⟨256668,20,(.group 1 395 true)⟩))
(.branch 256708
(.leaf ⟨256688,20,(.group 1 396 true)⟩)
(.leaf ⟨256708,20,(.group 1 397 true)⟩)))
(.branch 256768
(.branch 256748
(.leaf ⟨256728,20,(.group 1 398 true)⟩)
(.leaf ⟨256748,20,(.group 1 399 true)⟩))
(.branch 256788
(.leaf ⟨256768,20,(.group 1 400 true)⟩)
(.leaf ⟨256788,20,(.group 1 401 true)⟩))))
(.branch 256888
(.branch 256848
(.branch 256828
(.leaf ⟨256808,20,(.group 1 402 true)⟩)
(.leaf ⟨256828,20,(.group 1 403 true)⟩))
(.branch 256868
(.leaf ⟨256848,20,(.group 1 404 true)⟩)
(.leaf ⟨256868,20,(.group 1 405 true)⟩)))
(.branch 256928
(.branch 256908
(.leaf ⟨256888,20,(.group 1 406 true)⟩)
(.leaf ⟨256908,20,(.group 1 407 true)⟩))
(.branch 256948
(.leaf ⟨256928,20,(.group 1 408 true)⟩)
(.leaf ⟨256948,20,(.group 1 409 true)⟩)))))))

theorem tree237_checked : tree237.check 255706 256968 = true := by decide +kernel

def tree238 : Tree := (.branch 257608
(.branch 257288
(.branch 257128
(.branch 257048
(.branch 257008
(.branch 256988
(.leaf ⟨256968,20,(.group 1 410 true)⟩)
(.leaf ⟨256988,20,(.group 1 411 true)⟩))
(.branch 257028
(.leaf ⟨257008,20,(.group 1 412 true)⟩)
(.leaf ⟨257028,20,(.group 1 413 true)⟩)))
(.branch 257088
(.branch 257068
(.leaf ⟨257048,20,(.group 1 414 true)⟩)
(.leaf ⟨257068,20,(.group 1 415 true)⟩))
(.branch 257108
(.leaf ⟨257088,20,(.group 1 416 true)⟩)
(.leaf ⟨257108,20,(.group 1 417 true)⟩))))
(.branch 257208
(.branch 257168
(.branch 257148
(.leaf ⟨257128,20,(.group 1 418 true)⟩)
(.leaf ⟨257148,20,(.group 1 419 true)⟩))
(.branch 257188
(.leaf ⟨257168,20,(.group 1 420 true)⟩)
(.leaf ⟨257188,20,(.group 1 421 true)⟩)))
(.branch 257248
(.branch 257228
(.leaf ⟨257208,20,(.group 1 422 true)⟩)
(.leaf ⟨257228,20,(.group 1 423 true)⟩))
(.branch 257268
(.leaf ⟨257248,20,(.group 1 424 true)⟩)
(.leaf ⟨257268,20,(.group 1 425 true)⟩)))))
(.branch 257448
(.branch 257368
(.branch 257328
(.branch 257308
(.leaf ⟨257288,20,(.group 1 426 true)⟩)
(.leaf ⟨257308,20,(.group 1 427 true)⟩))
(.branch 257348
(.leaf ⟨257328,20,(.group 1 428 true)⟩)
(.leaf ⟨257348,20,(.group 1 429 true)⟩)))
(.branch 257408
(.branch 257388
(.leaf ⟨257368,20,(.group 1 430 true)⟩)
(.leaf ⟨257388,20,(.group 1 431 true)⟩))
(.branch 257428
(.leaf ⟨257408,20,(.group 1 432 true)⟩)
(.leaf ⟨257428,20,(.group 1 433 true)⟩))))
(.branch 257528
(.branch 257488
(.branch 257468
(.leaf ⟨257448,20,(.group 1 434 true)⟩)
(.leaf ⟨257468,20,(.group 1 435 true)⟩))
(.branch 257508
(.leaf ⟨257488,20,(.group 1 436 true)⟩)
(.leaf ⟨257508,20,(.group 1 437 true)⟩)))
(.branch 257568
(.branch 257548
(.leaf ⟨257528,20,(.group 1 438 true)⟩)
(.leaf ⟨257548,20,(.group 1 439 true)⟩))
(.branch 257588
(.leaf ⟨257568,20,(.group 1 440 true)⟩)
(.leaf ⟨257588,20,(.group 1 441 true)⟩))))))
(.branch 257931
(.branch 257768
(.branch 257688
(.branch 257648
(.branch 257628
(.leaf ⟨257608,20,(.group 1 442 true)⟩)
(.leaf ⟨257628,20,(.group 1 443 true)⟩))
(.branch 257668
(.leaf ⟨257648,20,(.group 1 444 true)⟩)
(.leaf ⟨257668,20,(.group 1 445 true)⟩)))
(.branch 257728
(.branch 257708
(.leaf ⟨257688,20,(.group 1 446 true)⟩)
(.leaf ⟨257708,20,(.group 1 447 true)⟩))
(.branch 257748
(.leaf ⟨257728,20,(.group 1 448 true)⟩)
(.leaf ⟨257748,20,(.group 1 449 true)⟩))))
(.branch 257848
(.branch 257808
(.branch 257788
(.leaf ⟨257768,20,(.group 1 450 true)⟩)
(.leaf ⟨257788,20,(.group 1 451 true)⟩))
(.branch 257828
(.leaf ⟨257808,20,(.group 1 452 true)⟩)
(.leaf ⟨257828,20,(.group 1 453 true)⟩)))
(.branch 257889
(.branch 257868
(.leaf ⟨257848,20,(.group 1 454 true)⟩)
(.leaf ⟨257868,21,(.group 1 455 true)⟩))
(.branch 257910
(.leaf ⟨257889,21,(.group 1 456 true)⟩)
(.leaf ⟨257910,21,(.group 1 457 true)⟩)))))
(.branch 258099
(.branch 258015
(.branch 257973
(.branch 257952
(.leaf ⟨257931,21,(.group 1 458 true)⟩)
(.leaf ⟨257952,21,(.group 1 459 true)⟩))
(.branch 257994
(.leaf ⟨257973,21,(.group 1 460 true)⟩)
(.leaf ⟨257994,21,(.group 1 461 true)⟩)))
(.branch 258057
(.branch 258036
(.leaf ⟨258015,21,(.group 1 462 true)⟩)
(.leaf ⟨258036,21,(.group 1 463 true)⟩))
(.branch 258078
(.leaf ⟨258057,21,(.group 1 464 true)⟩)
(.leaf ⟨258078,21,(.group 1 465 true)⟩))))
(.branch 258183
(.branch 258141
(.branch 258120
(.leaf ⟨258099,21,(.group 1 466 true)⟩)
(.leaf ⟨258120,21,(.group 1 467 true)⟩))
(.branch 258162
(.leaf ⟨258141,21,(.group 1 468 true)⟩)
(.leaf ⟨258162,21,(.group 1 469 true)⟩)))
(.branch 258225
(.branch 258204
(.leaf ⟨258183,21,(.group 1 470 true)⟩)
(.leaf ⟨258204,21,(.group 1 471 true)⟩))
(.branch 258246
(.leaf ⟨258225,21,(.group 1 472 true)⟩)
(.leaf ⟨258246,21,(.group 1 473 true)⟩)))))))

theorem tree238_checked : tree238.check 256968 258267 = true := by decide +kernel

def tree239 : Tree := (.branch 258939
(.branch 258603
(.branch 258435
(.branch 258351
(.branch 258309
(.branch 258288
(.leaf ⟨258267,21,(.group 1 474 true)⟩)
(.leaf ⟨258288,21,(.group 1 475 true)⟩))
(.branch 258330
(.leaf ⟨258309,21,(.group 1 476 true)⟩)
(.leaf ⟨258330,21,(.group 1 477 true)⟩)))
(.branch 258393
(.branch 258372
(.leaf ⟨258351,21,(.group 1 478 true)⟩)
(.leaf ⟨258372,21,(.group 1 479 true)⟩))
(.branch 258414
(.leaf ⟨258393,21,(.group 1 480 true)⟩)
(.leaf ⟨258414,21,(.group 1 481 true)⟩))))
(.branch 258519
(.branch 258477
(.branch 258456
(.leaf ⟨258435,21,(.group 1 482 true)⟩)
(.leaf ⟨258456,21,(.group 1 483 true)⟩))
(.branch 258498
(.leaf ⟨258477,21,(.group 1 484 true)⟩)
(.leaf ⟨258498,21,(.group 1 485 true)⟩)))
(.branch 258561
(.branch 258540
(.leaf ⟨258519,21,(.group 1 486 true)⟩)
(.leaf ⟨258540,21,(.group 1 487 true)⟩))
(.branch 258582
(.leaf ⟨258561,21,(.group 1 488 true)⟩)
(.leaf ⟨258582,21,(.group 1 489 true)⟩)))))
(.branch 258771
(.branch 258687
(.branch 258645
(.branch 258624
(.leaf ⟨258603,21,(.group 1 490 true)⟩)
(.leaf ⟨258624,21,(.group 1 491 true)⟩))
(.branch 258666
(.leaf ⟨258645,21,(.group 1 492 true)⟩)
(.leaf ⟨258666,21,(.group 1 493 true)⟩)))
(.branch 258729
(.branch 258708
(.leaf ⟨258687,21,(.group 1 494 true)⟩)
(.leaf ⟨258708,21,(.group 1 495 true)⟩))
(.branch 258750
(.leaf ⟨258729,21,(.group 1 496 true)⟩)
(.leaf ⟨258750,21,(.group 1 497 true)⟩))))
(.branch 258855
(.branch 258813
(.branch 258792
(.leaf ⟨258771,21,(.group 1 498 true)⟩)
(.leaf ⟨258792,21,(.group 1 499 true)⟩))
(.branch 258834
(.leaf ⟨258813,21,(.group 1 500 true)⟩)
(.leaf ⟨258834,21,(.group 1 501 true)⟩)))
(.branch 258897
(.branch 258876
(.leaf ⟨258855,21,(.group 1 502 true)⟩)
(.leaf ⟨258876,21,(.group 1 503 true)⟩))
(.branch 258918
(.leaf ⟨258897,21,(.group 1 504 true)⟩)
(.leaf ⟨258918,21,(.group 1 505 true)⟩))))))
(.branch 260118
(.branch 260066
(.branch 259023
(.branch 258981
(.branch 258960
(.leaf ⟨258939,21,(.group 1 506 true)⟩)
(.leaf ⟨258960,21,(.group 1 507 true)⟩))
(.branch 259002
(.leaf ⟨258981,21,(.group 1 508 true)⟩)
(.leaf ⟨259002,21,(.group 1 509 true)⟩)))
(.branch 259065
(.branch 259044
(.leaf ⟨259023,21,(.group 1 510 true)⟩)
(.leaf ⟨259044,21,(.group 1 511 true)⟩))
(.branch 260064
(.leaf ⟨259065,999,.trap⟩)
(.leaf ⟨260064,2,(.free 1)⟩))))
(.branch 260084
(.branch 260073
(.branch 260069
(.leaf ⟨260066,3,(.free 2)⟩)
(.leaf ⟨260069,4,(.free 3)⟩))
(.branch 260078
(.leaf ⟨260073,5,(.free 4)⟩)
(.leaf ⟨260078,6,(.free 5)⟩)))
(.branch 260099
(.branch 260091
(.leaf ⟨260084,7,(.free 6)⟩)
(.leaf ⟨260091,8,(.free 7)⟩))
(.branch 260108
(.leaf ⟨260099,9,(.free 8)⟩)
(.leaf ⟨260108,10,(.free 9)⟩)))))
(.branch 260234
(.branch 260168
(.branch 260141
(.branch 260129
(.leaf ⟨260118,11,(.free 10)⟩)
(.leaf ⟨260129,12,(.free 11)⟩))
(.branch 260154
(.leaf ⟨260141,13,(.free 12)⟩)
(.leaf ⟨260154,14,(.free 13)⟩)))
(.branch 260199
(.branch 260183
(.leaf ⟨260168,15,(.free 14)⟩)
(.leaf ⟨260183,16,(.free 15)⟩))
(.branch 260216
(.leaf ⟨260199,17,(.free 16)⟩)
(.leaf ⟨260216,18,(.free 17)⟩))))
(.branch 260316
(.branch 260273
(.branch 260253
(.leaf ⟨260234,19,(.free 18)⟩)
(.leaf ⟨260253,20,(.free 19)⟩))
(.branch 260294
(.leaf ⟨260273,21,(.free 20)⟩)
(.leaf ⟨260294,22,(.free 21)⟩)))
(.branch 260363
(.branch 260339
(.leaf ⟨260316,23,(.free 22)⟩)
(.leaf ⟨260339,24,(.free 23)⟩))
(.branch 260388
(.leaf ⟨260363,25,(.free 24)⟩)
(.leaf ⟨260388,26,(.free 25)⟩)))))))

theorem tree239_checked : tree239.check 258267 260414 = true := by decide +kernel

def tree240 : Tree := (.branch 261098
(.branch 260693
(.branch 260528
(.branch 260469
(.branch 260441
(.leaf ⟨260414,27,(.free 26)⟩)
(.leaf ⟨260441,28,(.free 27)⟩))
(.branch 260498
(.leaf ⟨260469,29,(.free 28)⟩)
(.leaf ⟨260498,30,(.free 29)⟩)))
(.branch 260591
(.branch 260559
(.leaf ⟨260528,31,(.free 30)⟩)
(.leaf ⟨260559,32,(.free 31)⟩))
(.branch 260624
(.leaf ⟨260591,33,(.free 32)⟩)
(.branch 260658
(.leaf ⟨260624,34,(.free 33)⟩)
(.leaf ⟨260658,35,(.free 34)⟩)))))
(.branch 260883
(.branch 260766
(.branch 260729
(.leaf ⟨260693,36,(.free 35)⟩)
(.leaf ⟨260729,37,(.free 36)⟩))
(.branch 260804
(.leaf ⟨260766,38,(.free 37)⟩)
(.branch 260843
(.leaf ⟨260804,39,(.free 38)⟩)
(.leaf ⟨260843,40,(.free 39)⟩))))
(.branch 260966
(.branch 260924
(.leaf ⟨260883,41,(.free 40)⟩)
(.leaf ⟨260924,42,(.free 41)⟩))
(.branch 261009
(.leaf ⟨260966,43,(.free 42)⟩)
(.branch 261053
(.leaf ⟨261009,44,(.free 43)⟩)
(.leaf ⟨261053,45,(.free 44)⟩))))))
(.branch 261548
(.branch 261288
(.branch 261191
(.branch 261144
(.leaf ⟨261098,46,(.free 45)⟩)
(.leaf ⟨261144,47,(.free 46)⟩))
(.branch 261239
(.leaf ⟨261191,48,(.free 47)⟩)
(.leaf ⟨261239,49,(.free 48)⟩)))
(.branch 261389
(.branch 261338
(.leaf ⟨261288,50,(.free 49)⟩)
(.leaf ⟨261338,51,(.free 50)⟩))
(.branch 261441
(.leaf ⟨261389,52,(.free 51)⟩)
(.branch 261494
(.leaf ⟨261441,53,(.free 52)⟩)
(.leaf ⟨261494,54,(.free 53)⟩)))))
(.branch 261833
(.branch 261659
(.branch 261603
(.leaf ⟨261548,55,(.free 54)⟩)
(.leaf ⟨261603,56,(.free 55)⟩))
(.branch 261716
(.leaf ⟨261659,57,(.free 56)⟩)
(.branch 261774
(.leaf ⟨261716,58,(.free 57)⟩)
(.leaf ⟨261774,59,(.free 58)⟩))))
(.branch 261954
(.branch 261893
(.leaf ⟨261833,60,(.free 59)⟩)
(.leaf ⟨261893,61,(.free 60)⟩))
(.branch 262016
(.leaf ⟨261954,62,(.free 61)⟩)
(.branch 262079
(.leaf ⟨262016,63,(.free 62)⟩)
(.leaf ⟨262079,64,(.free 63)⟩)))))))

theorem tree240_checked : tree240.check 260414 262143 = true := by decide +kernel

def candidateTree : Tree := (.branch 117965 (.branch 60835 (.branch 37554 (.branch 18426 (.branch 8246 (.branch 3356 (.branch 924 tree0 (.branch 2151 tree1 tree2)) (.branch 5712 (.branch 4474 tree3 tree4) (.branch 6940 tree5 tree6))) (.branch 13286 (.branch 10730 (.branch 9452 tree7 tree8) (.branch 12042 tree9 tree10)) (.branch 15856 (.branch 14566 tree11 tree12) (.branch 17133 tree13 tree14)))) (.branch 27499 (.branch 22295 (.branch 19712 tree15 (.branch 20991 tree16 tree17)) (.branch 24882 (.branch 23588 tree18 tree19) (.branch 26162 tree20 tree21))) (.branch 32656 (.branch 30119 (.branch 28827 tree22 tree23) (.branch 31379 tree24 tree25)) (.branch 35122 (.branch 33866 tree26 tree27) (.branch 36333 tree28 tree29))))) (.branch 51431 (.branch 46190 (.branch 41247 (.branch 38775 tree30 (.branch 40010 tree31 tree32)) (.branch 43746 (.branch 42509 tree33 tree34) (.branch 44972 tree35 tree36))) (.branch 49639 (.branch 48697 (.branch 47455 tree37 tree38) (.branch 49191 tree39 tree40)) (.branch 50535 (.branch 50087 tree41 tree42) (.branch 50983 tree43 tree44)))) (.branch 55183 (.branch 52829 (.branch 51879 tree45 (.branch 52327 tree46 tree47)) (.branch 53950 (.branch 53374 tree48 tree49) (.branch 54543 tree50 tree51))) (.branch 57894 (.branch 56486 (.branch 55823 tree52 tree53) (.branch 57190 tree54 tree55)) (.branch 59302 (.branch 58598 tree56 tree57) (.branch 60067 tree58 tree59)))))) (.branch 87133 (.branch 73225 (.branch 66393 (.branch 63139 (.branch 61603 tree60 (.branch 62371 tree61 tree62)) (.branch 64729 (.branch 63907 tree63 tree64) (.branch 65561 tree65 tree66))) (.branch 69721 (.branch 68057 (.branch 67225 tree67 tree68) (.branch 68889 tree69 tree70)) (.branch 71433 (.branch 70553 tree71 tree72) (.branch 72329 tree73 tree74)))) (.branch 79497 (.branch 75913 (.branch 74121 tree75 (.branch 75017 tree76 tree77)) (.branch 77705 (.branch 76809 tree78 tree79) (.branch 78601 tree80 tree81))) (.branch 83293 (.branch 81373 (.branch 80413 tree82 tree83) (.branch 82333 tree84 tree85)) (.branch 85213 (.branch 84253 tree86 tree87) (.branch 86173 tree88 tree89))))) (.branch 102123 (.branch 93931 (.branch 90013 (.branch 88093 tree90 (.branch 89053 tree91 tree92)) (.branch 91933 (.branch 90973 tree93 tree94) (.branch 92907 tree95 tree96))) (.branch 98027 (.branch 95979 (.branch 94955 tree97 tree98) (.branch 97003 tree99 tree100)) (.branch 100075 (.branch 99051 tree101 tree102) (.branch 101099 tree103 tree104)))) (.branch 109291 (.branch 105195 (.branch 103147 tree105 (.branch 104171 tree106 tree107)) (.branch 107243 (.branch 106219 tree108 tree109) (.branch 108267 tree110 tree111))) (.branch 113613 (.branch 111437 (.branch 110349 tree112 tree113) (.branch 112525 tree114 tree115)) (.branch 115789 (.branch 114701 tree116 tree117) (.branch 116877 tree118 tree119))))))) (.branch 187825 (.branch 151724 (.branch 134444 (.branch 125581 (.branch 121229 (.branch 119053 tree120 (.branch 120141 tree121 tree122)) (.branch 123405 (.branch 122317 tree123 tree124) (.branch 124493 tree125 tree126))) (.branch 129933 (.branch 127757 (.branch 126669 tree127 tree128) (.branch 128845 tree129 tree130)) (.branch 132140 (.branch 131021 tree131 tree132) (.branch 133292 tree133 tree134)))) (.branch 142508 (.branch 137900 (.branch 135596 tree135 (.branch 136748 tree136 tree137)) (.branch 140204 (.branch 139052 tree138 tree139) (.branch 141356 tree140 tree141))) (.branch 147116 (.branch 144812 (.branch 143660 tree142 tree143) (.branch 145964 tree144 tree145)) (.branch 149420 (.branch 148268 tree146 tree147) (.branch 150572 tree148 tree149))))) (.branch 169556 (.branch 159828 (.branch 155180 (.branch 152876 tree150 (.branch 154028 tree151 tree152)) (.branch 157484 (.branch 156332 tree153 tree154) (.branch 158636 tree155 tree156))) (.branch 164692 (.branch 162260 (.branch 161044 tree157 tree158) (.branch 163476 tree159 tree160)) (.branch 167124 (.branch 165908 tree161 tree162) (.branch 168340 tree163 tree164)))) (.branch 178068 (.branch 173204 (.branch 170772 tree165 (.branch 171988 tree166 tree167)) (.branch 175636 (.branch 174420 tree168 tree169) (.branch 176852 tree170 tree171))) (.branch 182932 (.branch 180500 (.branch 179284 tree172 tree173) (.branch 181716 tree174 tree175)) (.branch 185364 (.branch 184148 tree176 tree177) (.branch 186580 tree178 tree179)))))) (.branch 226112 (.branch 207025 (.branch 196785 (.branch 191665 (.branch 189105 tree180 (.branch 190385 tree181 tree182)) (.branch 194225 (.branch 192945 tree183 tree184) (.branch 195505 tree185 tree186))) (.branch 201905 (.branch 199345 (.branch 198065 tree187 tree188) (.branch 200625 tree189 tree190)) (.branch 204465 (.branch 203185 tree191 tree192) (.branch 205745 tree193 tree194)))) (.branch 216385 (.branch 211009 (.branch 208321 tree195 (.branch 209665 tree196 tree197)) (.branch 213697 (.branch 212353 tree198 tree199) (.branch 215041 tree200 tree201))) (.branch 221762 (.branch 219073 (.branch 217729 tree202 tree203) (.branch 220417 tree204 tree205)) (.branch 224273 (.branch 223170 tree206 tree207) (.branch 225139 tree208 tree209))))) (.branch 240936 (.branch 233504 (.branch 228933 (.branch 227025 tree210 (.branch 227944 tree211 tree212)) (.branch 230991 (.branch 229935 tree213 tree214) (.branch 232164 tree215 tree216))) (.branch 237162 (.branch 236108 (.branch 235660 tree217 tree218) (.branch 236556 tree219 tree220)) (.branch 238893 (.branch 237973 tree221 tree222) (.branch 239887 tree223 tree224)))) (.branch 250895 (.branch 245616 (.branch 243188 (.branch 242036 tree225 tree226) (.branch 244390 tree227 tree228)) (.branch 248195 (.branch 246896 tree229 tree230) (.branch 249539 tree231 tree232))) (.branch 255706 (.branch 253344 (.branch 252267 tree233 tree234) (.branch 254494 tree235 tree236)) (.branch 258267 (.branch 256968 tree237 tree238) (.branch 260414 tree239 tree240))))))))

theorem candidateTree_checked : candidateTree.check 27 262143 = true := by

  simp only [candidateTree, Tree.check, Bool.and_eq_true, decide_eq_true_eq]

  norm_num only


  simp only [tree0_checked, tree1_checked, tree2_checked, tree3_checked, tree4_checked, tree5_checked, tree6_checked, tree7_checked, tree8_checked, tree9_checked, tree10_checked, tree11_checked, tree12_checked, tree13_checked, tree14_checked, tree15_checked, tree16_checked, tree17_checked, tree18_checked, tree19_checked, tree20_checked, tree21_checked, tree22_checked, tree23_checked, tree24_checked, tree25_checked, tree26_checked, tree27_checked, tree28_checked, tree29_checked, tree30_checked, tree31_checked, tree32_checked, tree33_checked, tree34_checked, tree35_checked, tree36_checked, tree37_checked, tree38_checked, tree39_checked, tree40_checked, tree41_checked, tree42_checked, tree43_checked, tree44_checked, tree45_checked, tree46_checked, tree47_checked, tree48_checked, tree49_checked, tree50_checked, tree51_checked, tree52_checked, tree53_checked, tree54_checked, tree55_checked, tree56_checked, tree57_checked, tree58_checked, tree59_checked, tree60_checked, tree61_checked, tree62_checked, tree63_checked, tree64_checked, tree65_checked, tree66_checked, tree67_checked, tree68_checked, tree69_checked, tree70_checked, tree71_checked, tree72_checked, tree73_checked, tree74_checked, tree75_checked, tree76_checked, tree77_checked, tree78_checked, tree79_checked, tree80_checked, tree81_checked, tree82_checked, tree83_checked, tree84_checked, tree85_checked, tree86_checked, tree87_checked, tree88_checked, tree89_checked, tree90_checked, tree91_checked, tree92_checked, tree93_checked, tree94_checked, tree95_checked, tree96_checked, tree97_checked, tree98_checked, tree99_checked, tree100_checked, tree101_checked, tree102_checked, tree103_checked, tree104_checked, tree105_checked, tree106_checked, tree107_checked, tree108_checked, tree109_checked, tree110_checked, tree111_checked, tree112_checked, tree113_checked, tree114_checked, tree115_checked, tree116_checked, tree117_checked, tree118_checked, tree119_checked, tree120_checked, tree121_checked, tree122_checked, tree123_checked, tree124_checked, tree125_checked, tree126_checked, tree127_checked, tree128_checked, tree129_checked, tree130_checked, tree131_checked, tree132_checked, tree133_checked, tree134_checked, tree135_checked, tree136_checked, tree137_checked, tree138_checked, tree139_checked, tree140_checked, tree141_checked, tree142_checked, tree143_checked, tree144_checked, tree145_checked, tree146_checked, tree147_checked, tree148_checked, tree149_checked, tree150_checked, tree151_checked, tree152_checked, tree153_checked, tree154_checked, tree155_checked, tree156_checked, tree157_checked, tree158_checked, tree159_checked, tree160_checked, tree161_checked, tree162_checked, tree163_checked, tree164_checked, tree165_checked, tree166_checked, tree167_checked, tree168_checked, tree169_checked, tree170_checked, tree171_checked, tree172_checked, tree173_checked, tree174_checked, tree175_checked, tree176_checked, tree177_checked, tree178_checked, tree179_checked, tree180_checked, tree181_checked, tree182_checked, tree183_checked, tree184_checked, tree185_checked, tree186_checked, tree187_checked, tree188_checked, tree189_checked, tree190_checked, tree191_checked, tree192_checked, tree193_checked, tree194_checked, tree195_checked, tree196_checked, tree197_checked, tree198_checked, tree199_checked, tree200_checked, tree201_checked, tree202_checked, tree203_checked, tree204_checked, tree205_checked, tree206_checked, tree207_checked, tree208_checked, tree209_checked, tree210_checked, tree211_checked, tree212_checked, tree213_checked, tree214_checked, tree215_checked, tree216_checked, tree217_checked, tree218_checked, tree219_checked, tree220_checked, tree221_checked, tree222_checked, tree223_checked, tree224_checked, tree225_checked, tree226_checked, tree227_checked, tree228_checked, tree229_checked, tree230_checked, tree231_checked, tree232_checked, tree233_checked, tree234_checked, tree235_checked, tree236_checked, tree237_checked, tree238_checked, tree239_checked, tree240_checked, and_self]


theorem candidate_lookup_good {s : Nat} (hlo : 27 ≤ s) (hhi : s < 262143) :
    Good (candidateTree.lookup s) ∧ (candidateTree.lookup s).entry ≤ s ∧
      s < (candidateTree.lookup s).entry + (candidateTree.lookup s).length :=
  Tree.lookup_good candidateTree candidateTree_checked hlo hhi
end OptimalOTS.FreeLastLayout
