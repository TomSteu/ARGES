(* Two Higgs Doublet Model - using Type II Yukawas *)
Needs["ARGES`"]
Reset[];
NumberOfSubgroups=3;
Gauge[g1, U, 1, {0, 1, 1}];
Gauge[g2, SU, 2, {0, 3, 1}];
Gauge[g3, SU, 3, {0, 1, 8}];
WeylFermion[Q, 3, { 1/6, 2, 3}];
WeylFermion[L, 3, {-1/2, 2, 1}];
WeylFermion[D, 3, {-1/3, 1, 3}];
WeylFermion[U, 3, {+ 2/3, 1, 3}];
WeylFermion[E, 3, {-1, 1, 1}];
ComplexScalar[H1, {1,1}, { +1/2, 2, 1}];
ComplexScalar[H2, {1,1}, { +1/2, 2, 1}];
VEV[v1, Re[H1], {1,1}, {1,1,1}, 1];
VEV[v2, Re[H2], {1,1}, {1,2,1}, 1];
YukawaYaij[Yd, H2, Q, D, {1 &, KroneckerDelta[#1, #2] &, KroneckerDelta[#2, #3] &}];
YukawaYaij[Ye, H2, L, E, {1 &, KroneckerDelta[#1, #2] &, 1 &}];
YukawaYaij[Yu, H1, Q, U, {1 &, KroneckerDelta[#1, #2] &, KroneckerDelta[#2, #3] &}];
Quartic\[Lambda]abcd[\[Lambda]1, adj[H1], H1, adj[H1], H1, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
Quartic\[Lambda]abcd[\[Lambda]2, adj[H2], H2, adj[H2], H2, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
Quartic\[Lambda]abcd[\[Lambda]3, adj[H1], H1, adj[H2], H2, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, (KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
Quartic\[Lambda]abcd[\[Lambda]4, adj[H1], H2, adj[H2], H1, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, (KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
Quartic\[Lambda]abcd[\[Lambda]5, adj[H1], H2, adj[H1], H2, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
Quartic\[Lambda]abcd[\[Lambda]5, adj[H2], H1, adj[H2], H1, {1&, (KroneckerDelta[#1, #2] KroneckerDelta[#3, #4])&, 1&}, 1/2(KroneckerDelta[#2,#3] KroneckerDelta[#1,#4] KroneckerDelta[#5,#8] KroneckerDelta[#6,#7])&];
ScalarMassMab[m112, adj[H1], H1, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
ScalarMassMab[m222, adj[H2], H2, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
ScalarMassMab[m122, adj[H1], H2, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
ScalarMassMab[m122, adj[H2], H1, {1&, KroneckerDelta[#1,#2]&, 1&}, 1&];
