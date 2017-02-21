Needs["ARGES`"]
Reset[];
NumberOfSubgroups = 3;
Eps[a_Integer, b_Integer] := If[a + b == 3 && a > 0 && b > 0, If[b == a + 1, 1, -1], 0];
Gauge[g1, U, 1, {0, 1, 1}];
Gauge[g2, SU, 2, {0, 3, 1}];
Gauge[g3, SU, 3, {0, 1, 8}];
WeylFermion[Q, 3, { 1/6, 2, 3}];
WeylFermion[L, 3, {-1/2, 2, 1}];
WeylFermion[D, 3, {-1/3, 1, 3}];
WeylFermion[U, 3, {+ 2/3, 1, 3}];
WeylFermion[E, 3, {-1, 1, 1}];
ComplexScalar[H, {1,1}, { +1/2, 2, 1}];
YukawaY[yt, H, Q, D, {1 &, KroneckerDelta[#1, #2] &, KroneckerDelta[#2, #3] &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,4])&];
YukawaY[ytau, H, L, E, {1 &, KroneckerDelta[#1, #2] &, 1 &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,3])&];
YukawaY[Yu, adj[H], Q, U, {1 &, Eps[#1, #2] &, KroneckerDelta[#2, #3] &}, (KroneckerDelta[#3,3] KroneckerDelta[#4,4])&];
Quartic\[Lambda]abcd[\[Lambda], adj[H], H, adj[H], H, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
ComputeInvariants[];
