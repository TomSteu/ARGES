BeginPackage["SARGES`"];
	Gauge::usage = "Specify gauge subgroup";
	ChiralSuperField::usage = "Specify Chiral Superfield";
	SuperYukawa::usage = "Add Superpotential Yukawa term";
	SuperMass::usage = "Add Superpotential mass term";
	SuperTadpole::usage = "Add Superpotential tadpole term";
	SoftTrilinear::usage = "Add Soft SUSY-breaking trilinear coupling";
	SoftBilinear::usage = "Add Soft SUSY-breaking bilinear coupling";
	SoftScalarMass::usage = "Add Soft SUSY-breaking scalar mass";
	GauginoMass::usage = "Add Soft SUSY-breaking gaugino mass";
	VEV::usage = "Add Vacuum expectation value";
	\[Gamma]::usage = "Anomalous dimensions for scalar or fermion fields";
	\[Beta]::usage = "Display coupling (LoopLevel = 0) or Beta function";
	Trilinear\[Beta]::usage = "Display soft scalar trilinear coupling (LoopLevel = 0) or its Beta function";
	Bilinear\[Beta]::usage = "Display soft scalar bilinear coupling (LoopLevel = 0) or its Beta function";
	ScalarMass\[Beta]::usage = "Display soft scalar mass parameter (LoopLevel = 0) or its Beta function";
	GauginoMass\[Beta]::usage = "Display gaugino mass parameter (LoopLevel = 0) or its Beta function";
	Reset::usage = "reset/initiate package";
	ComputeInvariants::usage = "Calculates known invariants for beta functions, saves them as rules in subInvariants";
	subInvariants::usage = "containts replacement rules for beta function invariants, use ComputeInvariants[] to calculate";
	SimplifyProduct::usage = "Simplifies tr[___] and prod[___] expressions";
	d::usage= "Dimension of Representation";
	C2::usage = "Casimir Invariant";
	S2::usage = "Dynkin Index";
	T2::usage = "Dynkin Index without Trace all particles";
	Y2::usage = "Yukawa Invariant";
	hY::usage = "Yukawa Invariant";
	prod::usage = "product of flavour matrices";
	adj::usage = "adjoint";
	conj::usage = "complex conjugate";
	transpose::usage = "transposition";
	tr::usage = "trace of flavour matrices";
	U::usage = "Unitary Group";
	SU::usage = "Special Unitary Group";
	SO::usage = "Special Orthogonal Group";
	\[CapitalLambda]::usage = "Product of Generators";
	\[Xi]::usage = "Gauge fixing constant";
	\[Zeta]::usage = "Zeta function";
	Generator::usage = "Gauge Generator";
	subSimplifySum::usage = "Rules for advanced Simplification";
	SimplifySum::usage = "Label for advanced Simplification, to be used only within subSimplifySum";

	
	Sqr[x_] := x*x;
	Eps[a_Integer, b_Integer] := (KroneckerDelta[a,1] KroneckerDelta[b,2] - KroneckerDelta[a,2] KroneckerDelta[b,1]);
	NumberOfSubgroups = 1;

	
	Begin["SARGESp`"];
		Reset[] := Block[
			{},
			ListGauge = {};
			ListVEV = {};
			ListSYukawa = {};
			ListSMass = {};
			ListSTadpole = {};
			ListSTriLin = {};
			ListSBiLin = {};
			ListSSMass = {};
			ListGMass = Table[0, {i, 1, NumberOfSubgroups}];
			ChiralSuperFieldList = {};
			subInvariants = {};
			nonNumerics = {};
			subSimplifySum = {};
			$Assumptions = Element[KroneckerDelta[___], Reals];
		];

		(* Interfaces to define the theory *)
		Gauge[sym_, group_, n_, reps_List] := Block[
			{},
			If[!NumberQ[NumberOfSubgroups] || !MatchQ[NumberOfSubgroups, _Integer] || NumberOfSubgroups<0, 
				Message[Gauge::NAN];
				Return[];
			];
			If[Dimensions[ListGauge][[1]] >= NumberOfSubgroups, 
				Message[Gauge::Full];
				Return[];
			];
			If[Dimensions[reps][[1]] != NumberOfSubgroups,
				Message[Gauge::RepMismatch];
				Return[];
			];
			AddAssumption[n];
			AddAssumptionGauge[reps];
			ListGauge = Append[ListGauge, {sym, group, n, reps}];
		];

		ChiralSuperField[sym_, Nflavor_, gauge_List] := Block[
			{},
			If[Dimensions[gauge][[1]] != NumberOfSubgroups, 
				Message[WeylFermion::RepMismatch];
				Return[];
			];
			If[IdxCheck[{Nflavor}],
				Message[Gen::RepInvalid];
				Return[];
			];
			If[GaugeIdxCheck[gauge],
				Message[Gauge::RepInvalid];
				Return[];
			];
			AddAssumption[Nflavor];
			AddAssumptionGauge[gauge];
			ChiralSuperFieldList = Append[ChiralSuperFieldList, {sym, Nflavor, gauge}];
		];
		
		VEV[sym_, Sa_, SGenIdx_, SGaugeIdx_List, fak_:1] := Block[
			{posS},
			posS  = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sa &)];
			If[posS == {},
				Message[Scalar::UnknownParticle];
				Return[];
			];
			If[IdxCheck[{SGenIdx}],
				Message[Gen::RepMismatch];
				Return[];
			];
			If[Dimensions[SGaugeIdx][[1]] != NumberOfSubgroups || GaugeIdxCheck[SGaugeIdx], 
				Message[Gauge::RepMismatch];
				Return[];
			];
			If[SuperIndexOut[posS[[1,1]], Join[{SGenIdx}, SGaugeIdx]],
				Message[Gen::RepMismatch];
				Message[Gauge::RepMismatch];
				Return[];
			];
			ListVEV = Append[ListVEV, {sym, fak, Join[{posS[[1,1]], SGenIdx}, SGaugeIdx]}];
		];

		SuperYukawa[sym_, Si_, Sj_, Sk_, gauge_List, fak_] := Block[
			{posSi, posSj, posSk, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			posSj = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sj &)];
			posSk = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sk &)];
			If[posSi == {} || posSj == {} || posSk == {},
				Message[Yukawa::UnknownParticle];,
				permList = {{#1, #2, #3}, {#1, #3, #2}, {#2, #1, #3}, {#2, #3, #1}, {#3, #1, #2}, {#3, #2, #1}};
				invPermList = {{#1, #2, #3}, {#1, #3, #2}, {#2, #1, #3}, {#3, #1, #2}, {#2, #3, #1}, {#3, #2, #1}};
				For[i=1, i<=6, i++, 
					ListSYukawa = Append[ListSYukawa, Join[
						{sym}, 
						Evaluate[invPermList[[i]]]&[posSi[[1,1]], posSj[[1,1]], posSk[[1,1]]],
						{Table[Evaluate[gauge[[j]]@@permList[[i]]]&, {j, 1, NumberOfSubgroups}]}, 
						{Evaluate[fak@@permList[[i]]]&}
					]];
				];
				SimplifySYukawaList[];
			];
		];

		SuperMass[sym_, Si_, Sj_, gauge_List, fak_] := Block[
			{posSi, posSj, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Mass::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			posSj = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sj &)];
			If[posSi == {} || posSj == {},
				Message[Mass::UnknownParticle];,
				permList = {{#1, #2}, {#2, #1}};
				For[i=1, i<=2, i++, 
					ListSMass = Append[ListSMass, Join[
						{sym}, 
						Evaluate[permList[[i]]]&[posSi[[1,1]], posSj[[1,1]]],
						{Table[Evaluate[gauge[[j]]@@permList[[i]]]&, {j, 1, NumberOfSubgroups}]}, 
						{Evaluate[fak@@permList[[i]]]&}
					]];
				];
				SimplifySMassList[];
			];
		];

		SuperTadpole[sym_, Si_,  gauge_List, fak_] := Block[
			{posSi, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Tadpole::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			If[posSi == {} || posSj == {},
				Message[Tadpole::UnknownParticle];,
				ListSTadpole = Append[ListSTad, {sym, posSi[[1,1]], gauge, fak}];
				SimplifySTadpoleList[];
			];
		];

		SoftTrilinear[sym_, Si_, Sj_, Sk_, gauge_List, fak_] := Block[
			{posSi, posSj, posSk, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Yukawa::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			posSj = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sj &)];
			posSk = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sk &)];
			If[posSi == {} || posSj == {} || posSk == {},
				Message[Yukawa::UnknownParticle];,
				permList = {{#1, #2, #3}, {#1, #3, #2}, {#2, #1, #3}, {#2, #3, #1}, {#3, #1, #2}, {#3, #2, #1}};
				invPermList = {{#1, #2, #3}, {#1, #3, #2}, {#2, #1, #3}, {#3, #1, #2}, {#2, #3, #1}, {#3, #2, #1}};
				For[i=1, i<=6, i++, 
					ListSTriLin = Append[ListSTriLin, Join[
						{sym}, 
						Evaluate[invPermList[[i]]]&[posSi[[1,1]], posSj[[1,1]], posSk[[1,1]]],
						{Table[Evaluate[gauge[[j]]@@permList[[i]]]&, {j, 1, NumberOfSubgroups}]}, 
						{Evaluate[fak@@permList[[i]]]&}
					]];
				];
				SimplifySTriLinList[];
			];
		];

		SoftBilinear[sym_, Si_, Sj_, gauge_List, fak_] := Block[
			{posSi, posSj, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Mass::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			posSj = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sj &)];
			If[posSi == {} || posSj == {},
				Message[Mass::UnknownParticle];,
				permList = {{#1, #2}, {#2, #1}};
				For[i=1, i<=2, i++, 
					ListSBiLin = Append[ListSBiLin, Join[
						{sym}, 
						Evaluate[permList[[i]]]&[posSi[[1,1]], posSj[[1,1]]],
						{Table[Evaluate[gauge[[j]]@@permList[[i]]]&, {j, 1, NumberOfSubgroups}]}, 
						{Evaluate[fak@@permList[[i]]]&}
					]];
				];
				SimplifySBiLinList[];
			];
		];

		SoftScalarMass[sym_, Si_, Sj_, gauge_List, fak_] := Block[
			{posSi, posSj, permList},
			If[Length[gauge] != NumberOfSubgroups,
				Message[Mass::ContractionError];
				Return[];
			];
			posSi = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Si &)];
			posSj = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == Sj &)];
			If[posSi == {} || posSj == {},
				Message[Mass::UnknownParticle];,
				ListSSMass = Append[ListSSMass, {sym,  posSi[[1,1]], posSj[[1,1]], gauge, fak}];
			];
		];

		GauginoMass[sym_, g_] := Block[
			{posG},
			posG = ListPosition[ListGauge,_List?(#[[1]] == g &)];
			If[posG == {},
				Message[Gauge::NoMem];,
				If[NumberOfSubgroups != Length[ListGMass],
					ListGMass = Table[If[i <= Length[ListGMass], ListGMass[[i]], 0], {i, 1, NumberOfSubgroups}];
				];
				ListGMass[[posG[[1,1]]]] += sym;
			];
		];

		SuperIndexOut[bos_, BList_] := (
			(NumberQ[ChiralSuperFieldList[[bos,2]]] && NumberQ[BList[[1]]] && ChiralSuperFieldList[[bos,2]] < BList[[1]] && IntegerQ[BList[[1]]] && BList[[1]] > 0) ||
			Or@@(Function[{x},(NumberQ[SMultiplicity[bos, x]] && NumberQ[BList[[1+x]]] && BList[[1+x]] > SMultiplicity[bos, x] && IntegerQ[BList[[1+x]]] && BList[[1+x]] > 0)]/@Range[NumberOfSubgroups])
		);


		
		(* clean up list of parameters by adding entries back together and then removing zero ones *)

		SimplifySYukawaList[] := Block[
			{ARG1, ARG2, ARG3},
			For[i=1, i<=Length[ListSYukawa]-1, Null,
				For[j=i+1, j<=Length[ListSYukawa], Null,
					If[ListSYukawa[[i, 1;;4]] === ListSYukawa[[j, 1;;4]] && And@@((# === 0)& /@ (Simplify/@((Apply[#, {ARG1, ARG2, ARG3}] /@ ListSYukawa[[i, 5]]) - (Apply[#, {ARG1, ARG2, ARG3}] /@ ListSYukawa[[i, 5]])))),
						If[ Simplify[ListSYukawa[[i, 6]][ARG1, ARG2, ARG3] + ListSYukawa[[j, 6]][ARG1, ARG2, ARG3]] === 0,
							ListSYukawa = Delete[ListSYukawa, j];
							ListSYukawa = Delete[ListSYukawa, i];
							j = i + 1;
							Continue[];,
							ListSYukawa[[i]] = Join[
								ListSYukawa[[i, 1;;5]],
								{Evaluate[Simplify[ListSYukawa[[i, 6]][ARG1, ARG2, ARG3] + ListSYukawa[[j, 6]][ARG1, ARG2, ARG3]] /. {ARG1->#1, ARG2->#2, ARG3->#3}]& }
							];
							ListSYukawa = Delete[ListSYukawa, j];
							Continue[];
						];
					];
					j++;
				];
				i++;
			];
		];

		SimplifySMassList[] := Block[
			{ARG1, ARG2},
			For[i=1, i<=Length[ListSMass]-1, Null,
				For[j=i+1, j<=Length[ListSMass], Null,
					If[ListSMass[[i, 1;;3]] === ListSMass[[j, 1;;3]] && And@@((# === 0)& /@ (Simplify/@((Apply[#, {ARG1, ARG2}] /@ ListSMass[[i, 4]]) - (Apply[#, {ARG1, ARG2}] /@ ListSMass[[i, 4]])))),
						If[ Simplify[ListSMass[[i, 5]][ARG1, ARG2] + ListSMass[[j, 5]][ARG1, ARG2]] === 0,
							ListSMass = Delete[ListSMass, j];
							ListSMass = Delete[ListSMass, i];
							j = i + 1;
							Continue[];,
							ListSMass[[i]] = Join[
								ListSMass[[i, 1;;4]],
								{Evaluate[Simplify[ListSMass[[i, 5]][ARG1, ARG2] + ListSMass[[j, 5]][ARG1, ARG2]] /. {ARG1->#1, ARG2->#2}]& }
							];
							ListSMass = Delete[ListSMass, j];
							Continue[];
						];
					];
					j++;
				];
				i++;
			];
		];

		SimplifySTadpoleList[] := Block[
			{ARG1},
			For[i=1, i<=Length[ListSTadpole]-1, Null,
				For[j=i+1, j<=Length[ListSTadpole], Null,
					If[ListSTadpole[[i, 1;;2]] === ListSTadpole[[j, 1;;2]] && And@@((# === 0)& /@ (Simplify/@((Apply[#, {ARG1}] /@ ListSTadpole[[i, 3]]) - (Apply[#, {ARG1}] /@ ListSTadpole[[i, 3]])))),
						If[ Simplify[ListSTadpole[[i, 4]][ARG1] + ListSTadpole[[j, 4]][ARG1]] === 0,
							ListSTadpole = Delete[ListSTadpole, j];
							ListSTadpole = Delete[ListSTadpole, i];
							j = i + 1;
							Continue[];,
							ListSTadpole[[i]] = Join[
								ListSTadpole[[i, 1;;3]],
								{Evaluate[Simplify[ListSTadpole[[i, 4]][ARG1] + ListSTadpole[[j, 4]][ARG1]] /. {ARG1->#1}]& }
							];
							ListSTadpole = Delete[ListSTadpole, j];
							Continue[];
						];
					];
					j++;
				];
				i++;
			];
		];

		SimplifySTriLinList[] := Block[
			{ARG1, ARG2, ARG3},
			For[i=1, i<=Length[ListSTriLin]-1, Null,
				For[j=i+1, j<=Length[ListSTriLin], Null,
					If[ListSTriLin[[i, 1;;4]] === ListSTriLin[[j, 1;;4]] && And@@((# === 0)& /@ (Simplify/@((Apply[#, {ARG1, ARG2, ARG3}] /@ ListSTriLin[[i, 5]]) - (Apply[#, {ARG1, ARG2, ARG3}] /@ ListSTriLin[[i, 5]])))),
						If[ Simplify[ListSTriLin[[i, 6]][ARG1, ARG2, ARG3] + ListSTriLin[[j, 6]][ARG1, ARG2, ARG3]] === 0,
							ListSTriLin = Delete[ListSTriLin, j];
							ListSTriLin = Delete[ListSTriLin, i];
							j = i + 1;
							Continue[];,
							ListSTriLin[[i]] = Join[
								ListSTriLin[[i, 1;;5]],
								{Evaluate[Simplify[ListSTriLin[[i, 6]][ARG1, ARG2, ARG3] + ListSTriLin[[j, 6]][ARG1, ARG2, ARG3]] /. {ARG1->#1, ARG2->#2, ARG3->#3}]& }
							];
							ListSTriLin = Delete[ListSTriLin, j];
							Continue[];
						];
					];
					j++;
				];
				i++;
			];
		];

		SimplifySBiLinList[] := Block[
			{ARG1, ARG2},
			For[i=1, i<=Length[ListSBiLin]-1, Null,
				For[j=i+1, j<=Length[ListSBiLin], Null,
					If[ListSBiLin[[i, 1;;3]] === ListSBiLin[[j, 1;;3]] && And@@((# === 0)& /@ (Simplify/@((Apply[#, {ARG1, ARG2}] /@ ListSBiLin[[i, 4]]) - (Apply[#, {ARG1, ARG2}] /@ ListSBiLin[[i, 4]])))),
						If[ Simplify[ListSBiLin[[i, 5]][ARG1, ARG2] + ListSBiLin[[j, 5]][ARG1, ARG2]] === 0,
							ListSBiLin = Delete[ListSBiLin, j];
							ListSBiLin = Delete[ListSBiLin, i];
							j = i + 1;
							Continue[];,
							ListSBiLin[[i]] = Join[
								ListSBiLin[[i, 1;;4]],
								{Evaluate[Simplify[ListSBiLin[[i, 5]][ARG1, ARG2] + ListSBiLin[[j, 5]][ARG1, ARG2]] /. {ARG1->#1, ARG2->#2}]& }
							];
							ListSBiLin = Delete[ListSBiLin, j];
							Continue[];
						];
					];
					j++;
				];
				i++;
			];
		];
		
		
		(* add assumptions for non-numeric input *)
		AddAssumption[sym_] := Block[
			{},
			If[NumberQ[sym], Return[];];
			If[MemberQ[nonNumerics,sym], Return[];];
			$Assumptions=$Assumptions&&Element[sym, Integers]&&(sym>1);
			nonNumerics = Append[nonNumerics,sym];
		];

		(* add assumptions for gauge list - fish out U(1) cases *)
		AddAssumptionGauge[symList] := Block[
			{i},
			If[Length[symList] > NumberOfSubgroups, Return[];];
			For[i=1, i <= Length[symList], i++,
				If[ListGauge[[i,3]] === 1, Coninue[];];
				AddAssumption[symList[[i]]];
			];
		];
		
		(* Check that indices are Integers *)
		
		IdxCheck[IdxList_] := Or@@((Function[{x}, (NumberQ[x] && !(IntegerQ[x] && (x>0)))])/@Flatten[IdxList]);
		
		GaugeIdxCheck[GaugeList_] := Block[
			{glist},
			If[ListGauge == {}, Return[False];];
			glist = GaugeList;
			For[ii = Dimensions[ListGauge][[1]], ii>=1, ii--,
				If[ListGauge[[ii,3]] === 1,
					glist=Delete[glist,ii];
				];
			];
			Return[Or@@((Function[{x}, (NumberQ[x] && !(IntegerQ[x] && (x>0)))])/@glist)];
		];
		
		
		(* Frontend for Beta functions *)
		
		(* gauge coupling and vev *)
		\[Beta][sym_, loop_] := Block[
			{pos},
			(* gauge coupling *)
			pos = ListPosition[ListGauge,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[BetaGauge[pos[[1,1]], loop]//SimplifyProduct];
			];
			(* VEV *)
			pos = ListPosition[ListVEV,_List?(#[[1]] == sym &)];
			If[pos != {}, 
				Return[BetaVEV[pos[[1,1]], loop]//SimplifyProduct];
			];
		];
		

		(* Yukawa coupling *)
		\[Beta][SType1_, SType2_, SType3_, SList1_List, SList2_List, SList3_List, loop_ ] := Block[
			{posS1, posS2, posS3},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			posS3 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType3 &)];
			If[posS1 == {} || posS2 == {} || posS3 == {},
				Message[Yukawa::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2] || SuperIndexOut[posS3[[1,1]], SList3],
				Return[0];
			];
			Return[BetaYukawa[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]],Prepend[SList3, posS3[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1 && Length[SList3] == NumberOfSubgroups + 1);
		

		(* Superfield Mass *)
		\[Beta][SType1_, SType2_, SList1_List, SList2_List, loop_ ] := Block[
			{posS1, posS2},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			If[posS1 == {} || posS2 == {} ,
				Message[Mass::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2],
				Return[0];
			];
			Return[BetaMass[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1);
		
		(* Superfield Tadpole *)
		\[Beta][SType1_, SList1_List, loop_ ] := Block[
			{posS1},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			If[posS1 == {},
				Message[Tadpole::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1],
				Return[0];
			];
			Return[BetaTadpole[Prepend[SList1, posS1[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1);


		(* Trilinear soft breaking parameter *)
		Trilinear\[Beta][SType1_, SType2_, SType3_, SList1_List, SList2_List, SList3_List, loop_ ] := Block[
			{posS1, posS2, posS3},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			posS3 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType3 &)];
			If[posS1 == {} || posS2 == {} || posS3 == {},
				Message[Yukawa::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2] || SuperIndexOut[posS3[[1,1]], SList3],
				Return[0];
			];
			Return[BetaTrilinear[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]],Prepend[SList3, posS3[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1 && Length[SList3] == NumberOfSubgroups + 1);


		(* Bilinear soft breaking parameter *)
		Bilinear\[Beta][SType1_, SType2_, SList1_List, SList2_List, loop_ ] := Block[
			{posS1, posS2},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			If[posS1 == {} || posS2 == {} ,
				Message[Mass::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2],
				Return[0];
			];
			Return[BetaBilinear[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1);


		(* Soft breaking scalar mass parameter *)
		ScalarMass\[Beta][SType1_, SType2_, SList1_List, SList2_List, loop_ ] := Block[
			{posS1, posS2},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			If[posS1 == {} || posS2 == {} ,
				Message[Mass::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2],
				Return[0];
			];
			Return[BetaSSMass[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1);

		(* Beta for Gaugino Masses *)
		GauginoMass\[Beta][gauge_, loop_] := Block[
			{pos},
			pos = ListPosition[ListGauge, _List?(#[[1]] == gauge &)];
			If[pos == {}, 
				Message[Gauge::NoMem];
				Return[];,
				Return[BetaGauginoMass[pos[[1,1]], loop]];
			];
		];


		(* Frontend for Gamma functions *)
		\[Gamma][SType1_, SType2_, SList1_List, SList2_List, loop_ ] := Block[
			{posS1, posS2},
			posS1 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType1 &)];
			posS2 = ListPosition[ChiralSuperFieldList, _List?(#[[1]] == SType2 &)];
			If[posS1 == {} || posS2 == {} ,
				Message[Mass::UnknownParticle];
				Return[];
			];
			If[SuperIndexOut[posS1[[1,1]], SList1] || SuperIndexOut[posS2[[1,1]], SList2],
				Return[0];
			];
			Return[SuperFieldGamma[Prepend[SList1, posS1[[1,1]]], Prepend[SList2, posS2[[1,1]]], loop]//SimplifyProduct];
		]/;(Length[SList1] == NumberOfSubgroups+1 && Length[SList2] == NumberOfSubgroups+1);

		
		(* Backend for Beta and Gamma functions *)
		(* We pick the notation beta_p = gamma.p - opposite to Martin, Vaughn *)

		SuperFieldGamma[s1_, s2_, 0] := TensorDelta[s1, s2];

		SuperFieldGamma[s1_, s2_, 1] := Block[
			{gamma=0},
			gamma += 1/2 SolveSuperProd[
				{conj[Yuk], Yuk}, 
				KroneckerDelta[#2, #5] KroneckerDelta[#3, #6]&, 6, {
					{1, Join[s2[[1;;2]], {s2[[3;;]]}]}, 
					{4, Join[s1[[1;;2]], {s1[[3;;]]}]}
				}
			];
			gamma += -2 TensorDelta[s1, s2] Sum[Power[ListGauge[[i,1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i,1]]], {i, 1, NumberOfSubgroups}];
			Return[gamma/Power[4 Pi, 2]];
		];

		SuperFieldGamma[s1_, s2_, 2] := Block[
			{gamma=0},
			gamma += -1/2 SolveSuperProd[
				{conj[Yuk], Yuk, conj[Yuk], Yuk}, 
				Evaluate[TensorDelta[{#2, #3, #5, #6, #9}, {#10, #4, #7, #8, #11}]]&,
				12,
				{
					{1, Join[s2[[1;;2]], {s2[[3;;]]}]},
					{12, Join[s1[[1;;2]], {s1[[3;;]]}]}
				}

			];
			gamma += Sum[
				Sum[Power[ListGauge[[i,1]], 2] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] SolveSuperProd[
					{conj[Yuk], Yuk, Delta[s3]},
					Evaluate[TensorDelta[{#3, #2, #5}, {#6, #7, #8}]]&,
					8,
					{
						{1, Join[s2[[1;;2]], {s2[[3;;]]}]}, 
						{4, Join[s1[[1;;2]], {s1[[3;;]]}]}
					}
				], 
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			gamma += 2 TensorDelta[s1, s2] Sum[C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i,1]]] ( 
				( S2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i,1]]] - 3 C2[ListGauge[[i,1]]] ) Power[ListGauge[[i,1]], 4] 
				+ Sum[ C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] Power[ListGauge[[i,1]] ListGauge[[j,1]], 2], {j, 1, NumberOfSubgroups}] 
			), {i, 1, NumberOfSubgroups}];
			
			Return[gamma/Power[4 Pi, 4]];
		];

		SuperFieldGamma[s1_, s2_, 3] := Block[
			{gamma=0, kappa=6 \[Zeta][3], B},
			B[g_] := 6 C2[ListGauge[[g, 1]]] - 2 Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}];
			gamma += Sum[
				C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]] TensorDelta[s1, s2] Power[ListGauge[[i, 1]], 6] (
					12 kappa Power[C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]], 2] -
					(2 kappa + 5) B[i] C2[ListGauge[[i, 1]]] +
					1/2 Power[B[i], 2] - 
					4 kappa Sum[
						S2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[j, 1]]],
						{s, 1, Length[ChiralSuperFieldList]},
						{j, 1, NumberOfSubgroups}
					]
				) - 10 C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]] TensorDelta[s1, s2] Power[ListGauge[[i, 1]], 4] (
					Sum[
						S2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] (1/2 Y2[s] - 2 Sum[Power[ListGauge[[j,1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[j, 1]]], {j, 1, NumberOfSubgroups}]),
						{s, 1, Length[ChiralSuperFieldList]}
					]
				) + TensorDelta[s1, s2] Sum[
					Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] (
						Power[ListGauge[[i, 1]], 2] (2 B[i] - kappa C2[ListGauge[[i, 1]]]) + 
						Power[ListGauge[[j, 1]], 2] (2 B[j] - kappa C2[ListGauge[[j, 1]]])
					),
					{j, 1, NumberOfSubgroups}
				],
				{i, 1, NumberOfSubgroups}
			];
			gamma += -10 kappa TensorDelta[s1, s2] Sum[
				Power[ListGauge[[i, 1]] ListGauge[[j, 1]] ListGauge[[k, 1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[k, 1]]],
				{i, 1, NumberOfSubgroups},
				{j, 1, NumberOfSubgroups},
				{k, 1, NumberOfSubgroups}
			];
			gamma += Power[4 Pi, 2] SuperFieldGamma[s1, s2, 1] Sum[
				(
					(- kappa C2[ListGauge[[i, 1]]] + B[i]) C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]] Power[ListGauge[[i, 1]], 4] + 
					(- 5 kappa + 8) Sum[Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]], {j, 1, NumberOfSubgroups}]
				),
				{i, 1, NumberOfSubgroups}
			];
			gamma += Sum[
				Sum[
					(
						Power[ListGauge[[i, 1]], 4] (- kappa C2[ListGauge[[i, 1]]] + 2 B[i]) C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] + 
						Sum[
							Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] (
								C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] (2 kappa - 4) +
								C2[ChiralSuperFieldList[[s, 1]], ListGauge[[j, 1]]] (-kappa - 12)
							),
							{j, 1, NumberOfSubgroups}
						] 
					),
					{i, 1, NumberOfSubgroups}
				] SolveSuperProd[
						{Yuk, Delta[s], conj[Yuk]},
						Evaluate[TensorDelta[{#2, #3, #5}, {#4, #8, #7}]]&,
						8,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{6, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				(
					(3 kappa - 2) Sum[
						C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s4, 1]], ListGauge[[j, 1]]] Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2],
						{i, 1, NumberOfSubgroups},
						{j, 1, NumberOfSubgroups}
					]
				) SolveSuperProd[
					{Yuk, Delta[s3], Delta[s4], conj[Yuk]},
					Evaluate[TensorDelta[{#2, #3, #5, #7}, {#4, #6, #8, #9}]]&,
					10,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{10, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s3, 1, Length[ChiralSuperFieldList]},
				{s4, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				Sum[
					(kappa - 4) Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]],
					{i, 1, NumberOfSubgroups}
				]
				SolveSuperProd[
					{Yuk, conj[Yuk], Delta[s], Yuk, conj[Yuk]},
					Evaluate[TensorDelta[{#3, #2, #6, #5, #8, #11}, {#13, #4, #10, #7, #9, #12}]]&,
					14,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				Sum[
					2 Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]],
					{i, 1, NumberOfSubgroups}
				]
				SolveSuperProd[
					{Yuk, conj[Yuk], Yuk, Delta[s], conj[Yuk]},
					Evaluate[TensorDelta[{#3, #2, #5, #6, #9, #11}, {#13, #4, #7, #8, #10, #12}]]&,
					14,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				Sum[
					kappa Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]],
					{i, 1, NumberOfSubgroups}
				]
				SolveSuperProd[
					{Yuk, Delta[s], conj[Yuk], Yuk, conj[Yuk]},
					Evaluate[TensorDelta[{#3, #2, #5, #7, #8, #11}, {#13, #4, #6, #9, #10, #12}]]&,
					14,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				Sum[
					(1 - kappa/2) Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]],
					{i, 1, NumberOfSubgroups}
				]
				SolveSuperProd[
					{Yuk, Delta[s], conj[Yuk], Yuk, conj[Yuk]},
					Evaluate[TensorDelta[{#2, #5, #3, #7, #8, #11}, {#4, #13, #6, #9, #10, #12}]]&,
					14,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			gamma += Sum[
				(kappa + 4) Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]],
				{i, 1, NumberOfSubgroups}
			] SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#2, #3, #5, #6, #9}, {#11, #4, #7, #8, #10}]]&,
				12,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{12, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			gamma += -1/4 SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#2, #3, #5, #6, #9, #11, #12, #15}, {#17, #4, #7, #8, #10, #13, #14, #16}]]&,
				18,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{18, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			gamma += -1/8 SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#2, #5, #6, #9, #3, #11, #12, #15}, {#4, #7, #8, #16, #10, #13, #14, #17}]]&,
				18,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{18, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			gamma += SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#2, #3, #5, #6, #8, #9, #12, #15}, {#17, #4, #14, #7, #10, #11, #13, #16}]]&,
				18,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{18, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			gamma += kappa/4 SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#2, #3, #5, #6, #8, #9, #10, #13}, {#4, #7, #11, #14, #12, #15, #16, #17}]]&,
				18,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{18, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			Return[gamma/Power[4 Pi, 6]];
		];

		BetaGauge[g_, 0] := ListGauge[[g, 1]];

		BetaGauge[g_, 1] := Block[
			{beta = 0},
			beta += -3 Power[ListGauge[[g, 1]], 3] C2[ListGauge[[g, 1]]];
			beta += Power[ListGauge[[g, 1]], 3] Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}];
			Return[beta/Power[4 Pi, 2]];
		];

		BetaGauge[g_, 2] := Block[
			{beta = 0},
			beta += -6 Power[ListGauge[[g, 1]], 5] Power[C2[ListGauge[[g, 1]]], 2];
			beta += 2 Power[ListGauge[[g, 1]], 5] C2[ListGauge[[g, 1]]] Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}];
			beta += 4 Power[ListGauge[[g, 1]], 3] Sum[Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}, {i, 1, NumberOfSubgroups}];
			beta += - Power[ListGauge[[g, 1]], 3]/d[ListGauge[[g, 1]]] Sum[ C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] Y2[s], {s, 1, Length[ChiralSuperFieldList]}];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaGauge[g_, 3] := Block[
			{
				beta = 0,
				Q
			},
			For[k=1, k<=NumberOfSubgroups, k++, 
				Q[k] = - 3 C2[ListGauge[[k, 1]]] + Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[k, 1]]], {s, 1, Length[ChiralSuperFieldList]}]
			];
			beta += 3/(2 d[ListGauge[[g, 1]]]) Power[ListGauge[[g, 1]], 3] Sum[
				C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] SolveSuperProd[
					{Yuk, Delta[s], conj[Yuk], Yuk, conj[Yuk]},
					Evaluate[TensorDelta[{#1, #2, #5, #3, #7, #8, #11}, {#14, #4, #13, #6, #9, #10, #12}]]&,
					14, {}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			beta += 1/(4 d[ListGauge[[g, 1]]]) Power[ListGauge[[g, 1]], 3] Sum[
				C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] SolveSuperProd[
					{Delta[s], Yuk, conj[Yuk], Yuk, conj[Yuk]},
					Evaluate[TensorDelta[{#1, #2, #4, #5, #8, #10, #11}, {#14, #3, #6, #7, #9, #12, #13}]]&,
					14, {}
				],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			beta += -6/d[ListGauge[[g, 1]]] Sum[
				Sum[
					Power[ListGauge[[g, 1]], 3] Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s1, 1]], ListGauge[[g, 1]]] C2[ChiralSuperFieldList[[s2, 1]], ListGauge[[i, 1]]] SolveSuperProd[
						{Yuk, Delta[s1], Delta[s2], conj[Yuk]},
						Evaluate[TensorDelta[{#1, #2, #5, #3, #7}, {#10, #4, #9, #6, #8}]]&,
						10, {}
					],
					{i, 1, NumberOfSubgroups}
				],
				{s1, 1, Length[ChiralSuperFieldList]},
				{s2, 1, Length[ChiralSuperFieldList]}
			];
			beta += 1/d[ListGauge[[g, 1]]] Sum[
				(
					- 2 Power[ListGauge[[g, 1]], 5] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] C2[ListGauge[[g, 1]]]
					+ Sum[Power[ListGauge[[g, 1]], 3] Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]], {i, 1, NumberOfSubgroups}]
				) Y2[s],
				{s, 1, Length[ChiralSuperFieldList]}
			];
			beta += -8 Sum[
				ListGauge[[g, 1]] Power[ListGauge[[g, 1]] ListGauge[[i, 1]] ListGauge[[j, 1]], 2] S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[j, 1]]],
				{s, 1, Length[ChiralSuperFieldList]},
				{i, 1, NumberOfSubgroups},
				{j, 1, NumberOfSubgroups}
			];
			beta += 8 Sum[
				Power[ListGauge[[g, 1]], 5] Power[ListGauge[[i, 1]], 2] C2[ListGauge[[g, 1]]] S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]],
				{s, 1, Length[ChiralSuperFieldList]},
				{i, 1, NumberOfSubgroups}
			];
			beta += -6 Sum[
				Power[ListGauge[[g, 1]], 3] Power[ListGauge[[i, 1]], 4] S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] Q[i],
				{s, 1, Length[ChiralSuperFieldList]},
				{i, 1, NumberOfSubgroups}
			];
			beta += Power[ListGauge[[g, 1]], 7] Q[g] C2[ListGauge[[g, 1]]] (4 C2[ListGauge[[g, 1]]] - Q[g]);
			Return[beta/Power[4 Pi, 6]];
		];

		BetaYukawa[s1_, s2_, s3_, 0] := SolveSuperProd[ {Yuk}, 1&, 3, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}, {2, Join[s2[[1;;2]], {s2[[3;;]]}]}, {3, Join[s3[[1;;2]], {s3[[3;;]]}]}}];
		
		BetaYukawa[s1_, s2_, s3_, n_] := (Simplify[(BetaGamma[s1, s2, s3, n] + BetaGamma[s2, s3, s1, n] + BetaGamma[s3, s1, s2, n]) //. {
				BetaGamma[A___, x1_, x2_  B___ , m_] :> BetaGamma[A, x2, x1, B, m] /; (x1[[1]] > x2[[1]])
			}] /. BetaGamma[y1_, y2_, y3_, l_] :> GammaYukawa[y1, y2, y3, l] 
		);

		GammaYukawa[s1_, s2_, s3_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6}, {#4, #8, #9}]]&,
				9,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{7, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += -2 Sum[Power[ListGauge[[i,1]], 2] C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i,1]]] BetaYukawa[s1, s2, s3, 0], {i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 2]];
		];

		GammaYukawa[s1_, s2_, s3_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #12}, {#4, #13, #7, #10, #11, #14}]]&,
				15,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{15, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += Sum[ Sum[Power[ListGauge[[i,1]], 2] (2 C2[ChiralSuperFieldList[[s4, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, Delta[s4]},
				Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #10, #9, #11}]]&,
				11,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{7, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			], {s4, 1, Length[ChiralSuperFieldList]}];
			beta += 2 BetaYukawa[s1, s2, s3, 0] Sum[
				C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2] ( 
					- 3 C2[ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2]
					+ Sum[ S2[ChiralSuperFieldList[[s4, 1]], ListGauge[[i,1]]], {s4, 1, Length[ChiralSuperFieldList]}] Power[ListGauge[[i,1]], 2]
					+ 2 Sum[ C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[j, 1]]] Power[ListGauge[[j,1]], 2], {j, 1, NumberOfSubgroups}] 
				), 
				{i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaMass[s1_, s2_, 0] := SolveSuperProd[ {SMass}, 1&, 2, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}, {2, Join[s2[[1;;2]], {s2[[3;;]]}]}}];

		BetaMass[s1_, s2_, n_] := If[s1 === s2, 2 GammaMass[s1, s2, n],  GammaMass[s1, s2, n] + GammaMass[s2, s1, n]]

		GammaMass[s1_, s2_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{SMass, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5}, {#3, #7, #8}]]&,
				8,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{6, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -2 Sum[Power[ListGauge[[i,1]], 2] C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i,1]]] BetaMass[s1, s2, 0], {i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 2]];
		];

		GammaMass[s1_, s2_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{SMass, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5, #7, #8, #11}, {#3, #12, #6, #9, #10, #13}]]&,
				14,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += Sum[ Sum[Power[ListGauge[[i,1]], 2] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] SolveSuperProd[
				{SMass, conj[Yuk], Yuk, Delta[s3]},
				Evaluate[TensorDelta[{#2, #4, #5, #7}, {#3, #9, #8, #10}]]&,
				10,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{6, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			], {s3, 1, Length[ChiralSuperFieldList]}];
			beta += 2 BetaMass[s1, s2, 0] Sum[
				C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2] ( 
					- 3 C2[ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2]
					+ Sum[ S2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i,1]]], {s3, 1, Length[ChiralSuperFieldList]}] Power[ListGauge[[i,1]], 2]
					+ 2 Sum[ C2[ChiralSuperFieldList[[s2[[1]], 1]], ListGauge[[j, 1]]] Power[ListGauge[[j,1]], 2], {j, 1, NumberOfSubgroups}] 
				), 
				{i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaTadpole[s1_, 0] := SolveSuperProd[ {STad}, 1&, 1, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}}];

		BetaTadpole[s1_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{STad, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#1, #3, #4}, {#2, #6, #7}]]&,
				7,
				{
						{5, Join[s1[[1;;2]], {s1[[3;;]]}]}
				}
			];
			beta += -2 Sum[Power[ListGauge[[i,1]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i,1]]] BetaTadpole[s1, 0], {i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 2]];
		];

		BetaTadpole[s1_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{STad, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#1, #3, #4, #6, #7, #10}, {#2, #11, #5, #8, #9, #12}]]&,
				13,
				{
						{13, Join[s1[[1;;2]], {s1[[3;;]]}]}
				}
			];
			beta += Sum[ Sum[Power[ListGauge[[i,1]], 2] (2 C2[ChiralSuperFieldList[[s2, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] SolveSuperProd[
				{STad, conj[Yuk], Yuk, Delta[s2]},
				Evaluate[TensorDelta[{#1, #3, #4, #6}, {#2, #8, #7, #9}]]&,
				9,
				{
						{5, Join[s1[[1;;2]], {s1[[3;;]]}]}
				}
			], {s2, 1, Length[ChiralSuperFieldList]}];
			beta += 2 BetaTadpole[s1, 0]  Sum[
				C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2] ( 
					- 3 C2[ListGauge[[i,1]]] Power[ListGauge[[i,1]], 2]
					+ Sum[ S2[ChiralSuperFieldList[[s2, 1]], ListGauge[[i,1]]], {s2, 1, Length[ChiralSuperFieldList]}] Power[ListGauge[[i,1]], 2]
					+ 2 Sum[ C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[j, 1]]] Power[ListGauge[[j,1]], 2], {j, 1, NumberOfSubgroups}] 
				), 
				{i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaGauginoMass[g_, 0] := ListGMass[[g]];

		BetaGauginoMass[g_, 1] := Block[
			{beta = 0},
			beta += -6 Power[ListGauge[[g, 1]], 2] ListGMass[[g]] C2[ListGauge[[g, 1]]];
			beta += 2 Power[ListGauge[[g, 1]], 2] ListGMass[[g]] Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}];
			Return[beta/Power[4 Pi, 2]];
		];

		BetaGauginoMass[g_, 2] := Block[
			{beta = 0},
			beta += -24 Power[ListGauge[[g, 1]], 4] ListGMass[[g]] Power[C2[ListGauge[[g, 1]]], 2];
			beta += 8 Power[ListGauge[[g, 1]], 4] ListGMass[[g]] C2[ListGauge[[g, 1]]] Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}];
			beta += 8 Power[ListGauge[[g, 1]], 2] Sum[Power[ListGauge[[i, 1]], 2] (ListGMass[[g]] + ListGMass[[i]]) C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]] S2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]], {s, 1, Length[ChiralSuperFieldList]}, {i, 1, NumberOfSubgroups}];
			beta += -2 Power[ListGauge[[g, 1]], 2]/d[ListGauge[[g, 1]]] Sum[ C2[ChiralSuperFieldList[[s, 1]], ListGauge[[g, 1]]] (ListGMass[[g]] Y2[s] - hY[s]), {s, 1, Length[ChiralSuperFieldList]}];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaTrilinear[s1_, s2_, s3_, 0] := SolveSuperProd[ {STriLin}, 1&, 3, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}, {2, Join[s2[[1;;2]], {s2[[3;;]]}]}, {3, Join[s3[[1;;2]], {s3[[3;;]]}]}}];
		
		BetaTrilinear[s1_, s2_, s3_, n_] := (Simplify[(BetaGamma[s1, s2, s3, n] + BetaGamma[s2, s3, s1, n] + BetaGamma[s3, s1, s2, n]) //. {
				BetaGamma[A___, x1_, x2_  B___ , m_] :> BetaGamma[A, x2, x1, B, m] /; (x1[[1]] > x2[[1]])
			}] /. BetaGamma[y1_, y2_, y3_, l_] :> GammaTrilinear[y1, y2, y3, l] 
		);

		GammaTrilinear[s1_, s2_, s3_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{STriLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6}, {#4, #7, #8}]]&,
				9,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{9, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += SolveSuperProd[
				{Yuk, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#3, #5, #6}, {#4, #7, #8}]]&,
				9,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{9, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += -2 Sum[
				Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i,1]]] (
					BetaTrilinear[s1, s2, s3, 0] - 2 ListGMass[[i]] BetaYukawa[s1, s2, s3, 0]
				),
				{i, 1, NumberOfSubgroups}
			];
			Return[beta/Power[4 Pi, 2]];

		];

		GammaTrilinear[s1_, s2_, s3_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{STriLin, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #12}, {#4, #13, #7, #10, #11, #14}]]&,
				15,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{15, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{Yuk, conj[Yuk], Yuk, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #12}, {#4, #13, #7, #10, #11, #14}]]&,
				15,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{15, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{Yuk, conj[Yuk], STriLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #12}, {#4, #13, #7, #10, #11, #14}]]&,
				15,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
						{15, Join[s3[[1;;2]], {s3[[3;;]]}]}
				}
			];
			beta += Sum[
				Sum[Power[ListGauge[[i, 1]], 2]( 2 C2[ChiralSuperFieldList[[s4, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i, 1]]] ), {i, 1, NumberOfSubgroups}] (
					SolveSuperProd[
						{STriLin, conj[Yuk], Delta[s4], Yuk},
						Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #7, #10, #9}]]&,
						11,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
							{11, Join[s3[[1;;2]], {s3[[3;;]]}]}
						}

					] + 2 SolveSuperProd[
						{Yuk, conj[Yuk], Delta[s4], STriLin},
						Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #7, #10, #9}]]&,
						11,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
							{11, Join[s3[[1;;2]], {s3[[3;;]]}]}
						}

					]
				) - 2 Sum[Power[ListGauge[[i, 1]], 2] ListGMass[[i]] ( 2 C2[ChiralSuperFieldList[[s4, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i, 1]]] ), {i, 1, NumberOfSubgroups}] (
					SolveSuperProd[
						{Yuk, conj[Yuk], Delta[s4], Yuk},
						Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #7, #10, #9}]]&,
						11,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{2, Join[s2[[1;;2]], {s2[[3;;]]}]},
							{11, Join[s3[[1;;2]], {s3[[3;;]]}]}
						}
					]
				),
				{s4, 1, Length[ChiralSuperFieldList]}
			];
			beta += Sum[
				Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[i, 1]]] (2 BetaTrilinear[s1, s2, s3, 0] - 8 ListGMass[[i]] BetaYukawa[s1, s2, s3, 0]) (
					Power[ListGauge[[i, 1]], 2] Sum[S2[ChiralSuperFieldList[[s4, 1]], ListGauge[[i, 1]]], {s4, 1, Length[ChiralSuperFieldList]}] +
					2 Sum[Power[ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s3[[1]], 1]], ListGauge[[j, 1]]] , {j, 1, NumberOfSubgroups}] -
					3 Power[ListGauge[[i, 1]], 2] C2[ListGauge[[i, 1]]]
				), 
				{i, 1, NumberOfSubgroups}
			];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaBilinear[s1_, s2_, 0] := SolveSuperProd[ {SBiLin}, 1&, 2, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}, {2, Join[s2[[1;;2]], {s2[[3;;]]}]}}];

		BetaBilinear[s1_, s2_, n_] := If[s1 === s2, 2 GammaBilinear[s1, s2, n],  GammaBilinear[s1, s2, n] + GammaBilinear[s2, s1, n]]

		GammaBilinear[s1_, s2_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{SBiLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5}, {#3, #6, #7}]]&,
				8,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{8, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += 1/2 SolveSuperProd[
				{Yuk, conj[Yuk], SBiLin},
				Evaluate[TensorDelta[{#3, #5, #6}, {#4, #7, #8}]]&,
				8,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += SolveSuperProd[
				{SMass, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#2, #4, #5}, {#3, #6, #7}]]&,
				8,
				{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{8, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -2 Sum[Power[ListGauge[[i,1]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i,1]]] (BetaBilinear[s1, s2, 0] - 2 ListGMass[[i]] BetaMass[s1, s2, 0]), {i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 2]];
		];

		GammaBilinear[s1_, s2_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{SBiLin, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5, #6, #7, #11}, {#3, #12, #8, #9, #10, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -1/2 SolveSuperProd[
				{Yuk, conj[Yuk], SBiLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #10}, {#4, #7, #14, #11, #12, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -1/2 SolveSuperProd[
				{Yuk, conj[Yuk], SMass, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#3, #5, #6, #8, #9, #10}, {#4, #7, #14, #11, #12, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{SMass, conj[Yuk], STriLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5, #6, #7, #11}, {#3, #12, #8, #9, #10, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{SMass, conj[Yuk], Yuk, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#2, #4, #5, #6, #7, #11}, {#3, #12, #8, #9, #10, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{14, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += 2 Sum[
				Sum[Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]], {i, 1, NumberOfSubgroups}] SolveSuperProd[
					{Yuk, conj[Yuk], Delta[s3], SBiLin},
					Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #7, #10, #9}]]&,
					10,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += -2 Sum[
				Sum[Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] ListGMass[[i]], {i, 1, NumberOfSubgroups}] SolveSuperProd[
					{Yuk, conj[Yuk], Delta[s3], SMass},
					Evaluate[TensorDelta[{#3, #5, #6, #8}, {#4, #7, #10, #9}]]&,
					10,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += Sum[
				Sum[Power[ListGauge[[i, 1]], 2] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] (
					SolveSuperProd[
						{SBiLin, conj[Yuk], Delta[s3], Yuk},
						Evaluate[TensorDelta[{#2, #4, #5, #7}, {#3, #6, #9, #8}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{10, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] + 2 SolveSuperProd[
						{SMass, conj[Yuk], Delta[s3], STriLin},
						Evaluate[TensorDelta[{#2, #4, #5, #7}, {#3, #6, #9, #8}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{10, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					]
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += -2 Sum[
				Sum[Power[ListGauge[[i, 1]], 2] ListGMass[[i]] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), {i, 1, NumberOfSubgroups}] (
					SolveSuperProd[
						{SMass, conj[Yuk], Delta[s3], Yuk},
						Evaluate[TensorDelta[{#2, #4, #5, #7}, {#3, #6, #9, #8}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{10, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					]
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += Sum[
				Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]] (2 BetaBilinear[s1, s2, 0] - 8 ListGMass[[i]] BetaMass[s1, s2, 0]) (
					Power[ListGauge[[i, 1]], 2] Sum[S2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]], {s3, 1, Length[ChiralSuperFieldList]}] +
					2 Sum[Power[ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[j, 1]]] , {j, 1, NumberOfSubgroups}] -
					3 Power[ListGauge[[i, 1]], 2] C2[ListGauge[[i, 1]]]
				), 
				{i, 1, NumberOfSubgroups}
			];
			Return[beta/Power[4 Pi, 4]];
		];

		(* Convention: s1 is the lower index in Martin, Vaughn; contracting the complex conjugate scalar  *)
		BetaSSMass[s1_, s2_, 0] := SolveSuperProd[ {SSMass}, 1&, 2, { {1, Join[s1[[1;;2]], {s1[[3;;]]}]}, {2, Join[s2[[1;;2]], {s2[[3;;]]}]}}];

		BetaSSMass[s1_, s2_, 1] := Block[
			{beta=0},
			beta += 1/2 SolveSuperProd[
				{conj[Yuk], Yuk, SSMass},
				Evaluate[TensorDelta[{#2, #3, #6}, {#4, #5, #7}]]&,
				8,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{8, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += 1/2 SolveSuperProd[
				{Yuk, conj[Yuk], SSMass},
				Evaluate[TensorDelta[{#2, #3, #6}, {#4, #5, #8}]]&,
				8,
				{
					{7, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{1, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += 2 SolveSuperProd[
				{conj[Yuk], Yuk, SSMass},
				Evaluate[TensorDelta[{#2, #3, #6}, {#5, #8, #7}]]&,
				8,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += SolveSuperProd[
				{conj[STriLin], STriLin},
				Evaluate[TensorDelta[{#2, #3}, {#5, #6}]]&,
				6,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -8 TensorDelta[s1, s2] Sum[Power[ListGauge[[i, 1]] ListGMass[[i]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]], {i, 1, NumberOfSubgroups}];
			beta += 2 Sum[Power[ListGauge[[i, 1]], 2] SolveSuperProd[
				{Lambda[i], SSMass},
				Evaluate[TensorDelta[{#2, #4}, {#5, #6}]]&,
				6,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{3, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			], {i, 1, NumberOfSubgroups}];
			Return[beta/Power[4 Pi, 2]];
		];
		
		BetaSSMass[s1_, s2_, 2] := Block[
			{beta=0},
			beta += -1/2 SolveSuperProd[
				{SSMass, conj[Yuk], Yuk, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #4, #5, #7, #9, #10}, {#3, #6, #14, #11, #12, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{8, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -1/2 SolveSuperProd[
				{SSMass, Yuk, conj[Yuk], Yuk, conj[Yuk]},
				Evaluate[TensorDelta[{#1, #4, #5, #7, #9, #10}, {#3, #6, #14, #11, #12, #13}]]&,
				14,
				{
					{8, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{2, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{ conj[Yuk], Yuk, SSMass, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #3, #5, #7, #10, #11}, {#8, #6, #9, #12, #13, #14}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{ conj[Yuk], Yuk, SSMass, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #3, #5, #8, #10, #11}, {#12, #6, #7, #9, #13, #14}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{ conj[Yuk], Yuk, SSMass, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #3, #5, #6, #9, #10}, {#8, #14, #7, #11, #12, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -2 SolveSuperProd[
				{conj[Yuk], Yuk, conj[Yuk], Yuk, SSMass},
				Evaluate[TensorDelta[{#2, #3, #6, #8, #9, #12}, {#5, #10, #7, #11, #14, #13}]]&,
				14,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{conj[Yuk], Yuk, conj[STriLin], STriLin},
				Evaluate[TensorDelta[{#2, #3, #6, #8, #9}, {#5, #10, #7, #11, #12}]]&,
				12,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{conj[STriLin], STriLin, conj[Yuk], Yuk},
				Evaluate[TensorDelta[{#2, #3, #6, #8, #9}, {#5, #10, #7, #11, #12}]]&,
				12,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{conj[STriLin], Yuk, conj[Yuk], STriLin},
				Evaluate[TensorDelta[{#2, #3, #6, #8, #9}, {#5, #10, #7, #11, #12}]]&,
				12,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += -SolveSuperProd[
				{conj[Yuk], conj[STriLin], STriLin, Yuk},
				Evaluate[TensorDelta[{#2, #3, #6, #8, #9}, {#5, #10, #7, #11, #12}]]&,
				12,
				{
					{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
					{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
				}
			];
			beta += Sum[
				Sum[
					Power[ListGauge[[i, 1]], 2] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), 
					{i, 1, NumberOfSubgroups}
				](
					SolveSuperProd[
						{SSMass, conj[Yuk], Yuk, Delta[s3]},
						Evaluate[TensorDelta[{#2, #4, #5, #8}, {#3, #7, #9, #10}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{6, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] + SolveSuperProd[
						{conj[Yuk], Yuk, Delta[s3], SSMass},
						Evaluate[TensorDelta[{#2, #3, #6, #4}, {#5, #7, #8, #9}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{10, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] + 2 SolveSuperProd[
						{conj[STriLin], STriLin, Delta[s3]},
						Evaluate[TensorDelta[{#2, #3, #6}, {#5, #7, #8}]]&,
						8,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					]
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += -Sum[
				Sum[
					Power[ListGauge[[i, 1]], 2] ListGMass[[i]] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), 
					{i, 1, NumberOfSubgroups}
				](
					2 SolveSuperProd[
						{conj[STriLin], Yuk, Delta[s3]},
						Evaluate[TensorDelta[{#2, #3, #6}, {#5, #7, #8}]]&,
						8,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] + 2 SolveSuperProd[
						{conj[Yuk], STriLin, Delta[s3]},
						Evaluate[TensorDelta[{#2, #3, #6}, {#5, #7, #8}]]&,
						8,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					]
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += 4 Sum[
				Sum[
					Power[ListGauge[[i, 1]] ListGMass[[i]], 2] (2 C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), 
					{i, 1, NumberOfSubgroups}
				](
					SolveSuperProd[
						{conj[Yuk], Yuk, Delta[s3]},
						Evaluate[TensorDelta[{#2, #3, #6}, {#5, #7, #8}]]&,
						8,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					]
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += 4 Sum[
				Sum[
					Power[ListGauge[[i, 1]], 2] (C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]] - C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]]), 
					{i, 1, NumberOfSubgroups}
				](
					SolveSuperProd[
						{conj[Yuk], Yuk, SSMass, Delta[s3]},
						Evaluate[TensorDelta[{#2, #3, #8, #6}, {#5, #9, #10, #7}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] 
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += 4 Sum[
				Sum[
					Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]], 
					{i, 1, NumberOfSubgroups}
				](
					SolveSuperProd[
						{conj[Yuk], Yuk, SSMass, Delta[s3]},
						Evaluate[TensorDelta[{#2, #5, #3, #6}, {#9, #10, #8, #7}]]&,
						10,
						{
							{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
							{4, Join[s2[[1;;2]], {s2[[3;;]]}]}
						}
					] 
				),
				{s3, 1, Length[ChiralSuperFieldList]}
			];
			beta += -2 Sum[
				Power[ListGauge[[i, 1]], 2] SolveSuperProd[
					{Lambda[i], SSMass, conj[Yuk], Yuk},
					Evaluate[TensorDelta[{#2, #4, #6, #8, #9}, {#10, #5, #7, #11, #12}]]&,
					12,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{3, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{i, 1, NumberOfSubgroups}
			];
			beta += 8 Sum[
				Power[ListGauge[[i, 1]], 2] Sum[
					Power[ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s3, 1]], ListGauge[[j, 1]]], 
					{j, 1, NumberOfSubgroups}
				] SolveSuperProd[
					{Lambda[i], Delta[s3], SSMass},
					Evaluate[TensorDelta[{#2, #4, #6}, {#8, #5, #7}]]&,
					8,
					{
						{1, Join[s1[[1;;2]], {s1[[3;;]]}]}, 
						{3, Join[s2[[1;;2]], {s2[[3;;]]}]}
					}
				],
				{s3, 1, Length[ChiralSuperFieldList]},
				{i, 1, NumberOfSubgroups}
			];
			beta += 8 TensorDelta[s1, s2] Sum[
				Power[ListGauge[[i, 1]] ListGauge[[i, 1]] ListGMass[[i]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]] (
					3 Sum[S2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]], {s3, 1, Length[ChiralSuperFieldList]}] - 10 C2[ListGauge[[i, 1]]]
				), 
				{i, 1, NumberOfSubgroups}
			];
			beta += 16 TensorDelta[s1, s2] Sum[
				Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[j, 1]]] (
						2 Power[ListGMass[[i]], 2] + ListGMass[[i]] ListGMass[[j]]
					),
				{i, 1, NumberOfSubgroups},
				{j, 1, NumberOfSubgroups}
			];
			beta += 8 TensorDelta[s1, s2] Sum[
				If[
					ListGauge[[i, 3]] === 1,
					0,
					Power[ListGauge[[i, 1]], 4] C2[ChiralSuperFieldList[[s1[[1]], 1]], ListGauge[[i, 1]]] Sum[
						T2[ChiralSuperFieldList[[s3, 1]], ListGauge[[i, 1]]]/SMultiplicity[s3, i]  SolveSuperProd[
							{Delta[s3], SSMass},
							Evaluate[TensorDelta[{#1, #2}, {#4, #3}]]&,
							4,
							{}
						],
						{s3, 1, Length[ChiralSuperFieldList]}
					]
				], 
				{i, 1, NumberOfSubgroups}
			];
			beta += 8 TensorDelta[s1, s2] Sum[
				If[
					ListGauge[[i, 3]] === 1 && ListGauge[[j, 3]] === 1,
					Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] Sum[
						 ChiralSuperFieldList[[s1[[1]], 3, i]] ChiralSuperFieldList[[s1[[1]], 3, j]] ChiralSuperFieldList[[s3, 3, i]] ChiralSuperFieldList[[s4, 3, j]] SolveSuperProd[
							{Delta[s3], Delta[s4], SSMass},
							Evaluate[TensorDelta[{#1, #2, #4}, {#6, #3, #5}]]&,
							6,
							{}
						],
						{s3, 1, Length[ChiralSuperFieldList]},
						{s4, 1, Length[ChiralSuperFieldList]}
					],
					0
				], 
				{i, 1, NumberOfSubgroups},
				{j, 1, NumberOfSubgroups}
			];
			Return[beta/Power[4 Pi, 4]];
		];

		BetaVEV[va_, 0] := ListVEV[[va,2]] ListVEV[[va,1]];

		BetaVEV[va_, 1] := Block[
			{beta=0},
			beta += Sum[
				TensorDelta[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]] Sum[
					Power[ListGauge[[i,1]], 2] (1 + \[Xi]) C2[ChiralSuperFieldList[[ListVEV[[va, 3, 1]], 1]], ListGauge[[i, 1]]],
					{i, 1, NumberOfSubgroups}
				],
				{vb, 1, Length[ListVEV]}
			];
			beta += -1/2 Sum[ 
				ListVEV[[vb,2]] ListVEV[[vb,1]] SolveSuperProd[
					{conj[Yuk], Yuk},
					Evaluate[TensorDelta[{#2, #3}, {#5, #6}]]&,
					6,
					{
						{1, Join[ListVEV[[va, 3, 1;;2]], {ListVEV[[va, 3, 3;;]]}]}, 
						{4, Join[ListVEV[[vb, 3, 1;;2]], {ListVEV[[vb, 3, 3;;]]}]} 
					}
				],
				{vb, 1, Length[ListVEV]}
			];
			Return[beta/Power[4 Pi, 2]];
		];

		BetaVEV[va_, 2] := Block[
			{beta=0},
			beta += Sum[
				TensorDelta[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]] Sum[
					Power[ListGauge[[i, 1]], 4] C2[ChiralSuperFieldList[[ListVEV[[va, 3, 1]], 1]], ListGauge[[i, 1]]](
						(9/4 - 5/3 \[Xi] - 1/4 Power[\[Xi], 2] + (7 - \[Xi]) \[Xi]/2 ) C2[ListGauge[[i, 1]]] - 
						Sum[S2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]], {s, 1, Length[ChiralSuperFieldList]}]
					),
					{i, 1, NumberOfSubgroups}
				],
				{vb, 1, Length[ListVEV]}
			];
			beta += -Sum[
				TensorDelta[ListVEV[[va,3]], ListVEV[[vb,3]]] ListVEV[[vb,2]] ListVEV[[vb,1]] Sum[
					Power[ListGauge[[i, 1]] ListGauge[[j, 1]], 2] C2[ChiralSuperFieldList[[ListVEV[[va,3,1]], 1]], ListGauge[[i, 1]]] C2[ChiralSuperFieldList[[ListVEV[[va,3,1]], 1]], ListGauge[[j, 1]]](
						2 + 2 \[Xi] (1 - \[Xi])
					),
					{i, 1, NumberOfSubgroups},
					{j, 1, NumberOfSubgroups}
				],
				{vb, 1, Length[ListVEV]}
			];
			beta += (1 - \[Xi]) Sum[
				ListVEV[[vb,2]] ListVEV[[vb,1]] Sum[Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[ListVEV[[va, 3, 1]], 1]], ListGauge[[i, 1]]], {i, 1, NumberOfSubgroups}] SolveSuperProd[
					{conj[Yuk], Yuk},
					Evaluate[TensorDelta[{#2, #3}, {#5, #6}]]&,
					6,
					{
						{1, Join[ListVEV[[va, 3, 1;;2]], {ListVEV[[va, 3, 3;;]]}]},
						{4, Join[ListVEV[[vb, 3, 1;;2]], {ListVEV[[vb, 3, 3;;]]}]}
					}
				],
				{vb, 1, Length[ListVEV]}
			];
			beta += -2 Sum[
				ListVEV[[vb,2]] ListVEV[[vb,1]] Sum[Power[ListGauge[[i, 1]], 2] C2[ChiralSuperFieldList[[s, 1]], ListGauge[[i, 1]]], {i, 1, NumberOfSubgroups}] SolveSuperProd[
					{conj[Yuk], Delta[s], Yuk},
					Evaluate[TensorDelta[{#2, #5, #3}, {#4, #7, #8}]]&,
					8,
					{
						{1, Join[ListVEV[[va, 3, 1;;2]], {ListVEV[[va, 3, 3;;]]}]},
						{6, Join[ListVEV[[vb, 3, 1;;2]], {ListVEV[[vb, 3, 3;;]]}]}
					}
				],
				{vb, 1, Length[ListVEV]},
				{s, 1, Length[ChiralSuperFieldList]}
			];
			beta += 1/2 Sum[
				ListVEV[[vb,2]] ListVEV[[vb,1]] SolveSuperProd[
					{conj[Yuk], Yuk, conj[Yuk], Yuk},
					Evaluate[TensorDelta[{#2, #3, #5, #6, #9}, {#4, #11, #7, #8, #12}]]&,
					12,
					{
						{1, Join[ListVEV[[va, 3, 1;;2]], {ListVEV[[va, 3, 3;;]]}]},
						{10, Join[ListVEV[[vb, 3, 1;;2]], {ListVEV[[vb, 3, 3;;]]}]}
					}
				],
				{vb, 1, Length[ListVEV]}
			];
			Return[beta/Power[4 Pi, 4]];
		];

		
		(* Definition of Invariants related to the gauge group*)
		ComputeInvariants[] := Block[
			{i, f, s, sIdx, Y4Hold, assHold},
			subInvariants = {};
			If[NumberOfSubgroups==0 || Length[ListGauge], Return[];];
			For[i=1, i<=NumberOfSubgroups, i++,
				(* Gauge Boson Invariants *)
				If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1 && ListGauge[[i,4,i]] === 0,
					(* Singulet U(1) *)
					subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->1];
					subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->0];,
					(* not U(1) *)
					If[ListGauge[[i,4,i]] === 1,
						(* gauge singulet: *)
						subInvariants = Append[subInvariants, C2[ListGauge[[i]]]->0];,
						(* no singulet: *)
						(* Adjoint Rep in SU(N)*)
						If[ListGauge[[i,2]] === SU && ListGauge[[i,4,i]]===Sqr[ListGauge[[i,3]]]-1,
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->ListGauge[[i,3]]];
						];
						(* Adjoint Rep in SO(N)*)
						If[ListGauge[[i,2]] === SO && ListGauge[[i,4,i]]===1/2 ListGauge[[i,3]](ListGauge[[i,3]]-1),
							subInvariants = Append[subInvariants, d[ListGauge[[i,1]]]->ListGauge[[i,4,i]]];
							subInvariants = Append[subInvariants, C2[ListGauge[[i,1]]]->(2 ListGauge[[i,3]] - 4)];
						];
					];
				];
				(* Superfield invariants *)
				If[ChiralSuperFieldList != {},
					For[f=1, f<=Length[ChiralSuperFieldList], f++,
						subInvariants = Append[subInvariants, d[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->SMultiplicity[f,i]];
						subInvariants = Append[subInvariants, T2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->SMultiplicity[f,i]/SMultiplicity[f] S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]];
						(* SU(N) subgroup *)
						If[ListGauge[[i,2]] === SU,
							If[ChiralSuperFieldList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 1/2 (Sqr[ChiralSuperFieldList[[f,3,i]]]-1)/ChiralSuperFieldList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 1/2 SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === Sqr[ListGauge[[i,3]]] - 1,
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]] ListGauge[[i,3]]];
								];
								(* Symmetric Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1),
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] + 2)(ListGauge[[i,3]] - 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]] (1/2 ListGauge[[i,3]] + 1)];
								];
								(* Anitsymmetric Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === 1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 2)(ListGauge[[i,3]] + 1)/ListGauge[[i,3]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]] (1/2 ListGauge[[i,3]] - 1)];
								];
							];
						];
						(* SO(N) subgroup *)
						If[ListGauge[[i,2]] === SO,
							If[ChiralSuperFieldList[[f,3,i]] === 1,
								subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 0];
								subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 0];
								Continue[];,
								(* Fundamental Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === ListGauge[[i,3]],
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> (ListGauge[[i,3]] - 1)];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 2 SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]]];
								];
								(* Adjoint Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1),
									subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4)];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> (2 ListGauge[[i,3]] - 4) SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]]];
								];
								(* Symmetric Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] + 1) - 1,
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] + 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] + 1) - 1)];
								];
								(* Anitsymmetric Representation *)
								If[ChiralSuperFieldList[[f,3,i]] === 1/2 ListGauge[[i,3]](ListGauge[[i,3]] - 1) + 1,
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]-> 2(ListGauge[[i,3]] + 2) SMultiplicity[f]/ChiralSuperFieldList[[f,3,i]]];
									subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->ListGauge[[i,3]](ListGauge[[i,3]] - 1)(ListGauge[[i,3]] - 2)/(1/2 ListGauge[[i,3]] (ListGauge[[i,3]] - 1) + 1)];
								];
							];
						];
						(* U(1) subgroup *)
						If[ListGauge[[i,2]] === U && ListGauge[[i,3]] === 1,
							subInvariants = Append[subInvariants, C2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->Sqr[ChiralSuperFieldList[[f,3,i]]]];
							subInvariants = Append[subInvariants, S2[ChiralSuperFieldList[[f,1]], ListGauge[[i,1]]]->Sqr[ChiralSuperFieldList[[f,3,i]]] SMultiplicity[f]];
						];
					];
				];
			];
			(* SUSY Yukawa Invariants *)
			For[f=1, f<=Length[ChiralSuperFieldList], f++,
				subInvariants = Append[subInvariants, Y2[f]-> (
					SolveSuperProd[{Delta[f], Yuk, conj[Yuk]}, (Evaluate[TensorDelta[{#1, #2, #3, #4}, {#5, #8, #6, #7}]])&, 8, {}]
				)];
				subInvariants = Append[subInvariants, hY[f]-> (
					SolveSuperProd[{Delta[f], STriLin, conj[Yuk]}, (Evaluate[TensorDelta[{#1, #2, #3, #4}, {#5, #8, #6, #7}]])&, 8, {}]
				)];
			];
		];
		
		(* Kronecker delta for arbitray list of arguments*)
		TensorDelta[{},{}] := 1;
		TensorDelta[a_List, b_List] := KroneckerDelta[a[[1]], b[[1]]] TensorDelta[a[[2;;]], b[[2;;]]];
		
		(* Matrix multiplication and traces *)
		subProd := {
			prod[a___, b_ + c_, d___]:>(prod[a, b, d] + prod[a, c, d]),
			prod[][ii1_,ii2_]:>KroneckerDelta[ii1,ii2],
			prod[]:>1,
			prod[a_][ii1_,ii2_]:>a[ii1,ii2], 
			prod[a___, prod[b___], c___]:>prod[a, b, c], 
			prod[a___, n_, b___]:>(n prod[a,b])/; NumberQ[n],
			prod[a___, n_ c_, b___]:>(n prod[a,c,b])/; NumberQ[n],
			prod[a___, 0, b___]:>0,
			tr[a___, b_ + c_, d___]:>(tr[a, b, d] + tr[a, c, d]),
			tr[a___, n_, b___]:>(n tr[a,b])/; NumberQ[n], 
			tr[a___, n_ c_, b___]:>(n tr[a,c,b]) /; NumberQ[n], 
			tr[a___, 0, b___]:>0,
			tr[a___, prod[b___], c___]:>tr[a,b,c],
			adj[tr[a___]]:>tr[adj[a]],
			adj[prod[a___]]:>prod[adj[a]],
			prod[adj[a__,b__]]:>prod[adj[b],adj[a]],
			tr[adj[a___,b___]]:>tr[adj[b],adj[a]],
			adj[n_ a_]:> (Conjugate[n] adj[a]) /; NumberQ[n],
			prod[a___, tr[b___], c___]:>(tr[b] prod[a,c]),
			tr[a___ prod[b___]]:>(a tr[b]),
			adj[a_][i1_, i2_]:>adj[a[i2, i1]],
			adj[adj[a_]]:>a,
			adj[a_+ b_] :> (adj[a] + adj[b]),
			adj[0]->0
		};


		(* Convenience functions for field multiplicities *)
		SMultiplicity[f_] := ChiralSuperFieldList[[f,2]] Times@@(Function[{x}, SMultiplicity[f, x]]/@Range[NumberOfSubgroups]);
		SMultiplicity[f_, g_] := If[ListGauge[[g,3]]===1, 1, ChiralSuperFieldList[[f,3,g]]];
		

		(* grand unified function to calc products and traces  *)
		(*
		** args		... list specifying what kind of coupling is at which position
		** contr 	... index contraction - one index per superfield is assumed
		** n 		... total number of indices involved
		** external	... list of indices that are external {position, {Field, Flavour, {Gauge1, ...}} }
		*)
		SolveSuperProd[args_List, contr_, n_, external_List] := Block[
			{
				SIdx, res, FIdx, GIdx,
				$Assumptions = $Assumptions && And@@Table[Element[SIdx[i], Integers] && SIdx[i]>0 && Element[SIdx[i], Integers] && SIdx[i]>0 && And@@Table[Element[GIdx[i,j], Integers] && GIdx[i,j]>0, {j, 1, NumberOfSubgroups}], {i, 1, n}]
			},

			SimplifySProd[p_] := (
				If[! MemberQ[{p}, SProd[a___][b___], Infinity], Return[p];];
				Return[
					SimplifySProd[
						p /. {
							SProd[A___, conj[SYukContr[a_, b_, c_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSYukawa[[i, 2]]] KroneckerDelta[b, ListSYukawa[[i, 3]]] KroneckerDelta[c, ListSYukawa[[i, 4]]] conj[ListSYukawa[[i, 1]]] SProd[A, conj[SYukawa[i]], B][C],
								{i, 1, Length[ListSYukawa]}
							],
							SProd[A___, SYukContr[a_, b_, c_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSYukawa[[i, 2]]] KroneckerDelta[b, ListSYukawa[[i, 3]]] KroneckerDelta[c, ListSYukawa[[i, 4]]] ListSYukawa[[i, 1]] SProd[A, SYukawa[i], B][C],
								{i, 1, Length[ListSYukawa]}
							],
							SProd[A___, conj[SMassContr[a_, b_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSMass[[i, 2]]] KroneckerDelta[b, ListSMass[[i, 3]]] conj[ListSMass[[i, 1]]] SProd[A, conj[SMass[i]], B][C],
								{i, 1, Length[ListSMass]}
							],
							SProd[A___, SMassContr[a_, b_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSMass[[i, 2]]] KroneckerDelta[b, ListSMass[[i, 3]]] ListSMass[[i, 1]] SProd[A, SMass[i], B][C],
								{i, 1, Length[ListSMass]}
							],
							SProd[A___, conj[STadContr[a_, b_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSTadpole[[i, 2]]] conj[ListSTadpole[[i, 1]]] SProd[A, conj[STadpole[i]], B][C],
								{i, 1, Length[ListSTadpole]}
							],
							SProd[A___, STadContr[a_, b_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSTadpole[[i, 2]]] ListSTadpole[[i, 1]] SProd[A, STadpole[i], B][C],
								{i, 1, Length[ListSTadpole]}
							],
							SProd[A___, conj[STriLinContr[a_, b_, c_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSTriLin[[i, 2]]] KroneckerDelta[b, ListSTriLin[[i, 3]]] KroneckerDelta[c, ListSTriLin[[i, 4]]] conj[ListSTriLin[[i, 1]]] SProd[A, conj[STriLin[i]], B][C],
								{i, 1, Length[ListSTriLin]}
							],
							SProd[A___, STriLinContr[a_, b_, c_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSTriLin[[i, 2]]] KroneckerDelta[b, ListSTriLin[[i, 3]]] KroneckerDelta[c, ListSTriLin[[i, 4]]] ListSTriLin[[i, 1]] SProd[A, STriLin[i], B][C],
								{i, 1, Length[ListSTriLin]}
							],
							SProd[A___, conj[SBiLinContr[a_, b_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSBiLin[[i, 2]]] KroneckerDelta[b, ListSBiLin[[i, 3]]] conj[ListSBiLin[[i, 1]]] SProd[A, conj[SBiLin[i]], B][C],
								{i, 1, Length[ListSBiLin]}
							],
							SProd[A___, SBiLinContr[a_, b_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSBiLin[[i, 2]]] KroneckerDelta[b, ListSBiLin[[i, 3]]] ListSBiLin[[i, 1]] SProd[A, SBiLin[i], B][C],
								{i, 1, Length[ListSBiLin]}
							],
							SProd[A___, conj[SSMassContr[a_, b_]], B___][C___] :> Sum[
								KroneckerDelta[a, ListSSMass[[i, 2]]] KroneckerDelta[b, ListSSMass[[i, 3]]] conj[ListSSMass[[i, 1]]] SProd[A, conj[SSMass[i]], B][C],
								{i, 1, Length[ListSSMass]}
							],
							SProd[A___, SSMassContr[a_, b_], B___][C___] :> Sum[
								KroneckerDelta[a, ListSSMass[[i, 2]]] KroneckerDelta[b, ListSSMass[[i, 3]]] ListSSMass[[i, 1]] SProd[A, SSMass[i], B][C],
								{i, 1, Length[ListSSMass]}
							],
							SProd[A___] :> FProd[A]
						} /. {
							SimplifySum[a_, b___] :> SimplifySum[Expand[a], b]
						} //. Join[subSum, subSimplifySum]
					]
				];
			);
			
			Refine[(SimplifySum@@Join[
				{Expand[((SProd@@args)@@(SIdx/@Range[n]) contr@@(SIdx/@Range[n])) /. Table[SIdx[external[[i,1]]] -> external[[i,2,1]], {i, 1, Length[external]}]]}, 
				({SIdx[#], 1, Length[ChiralSuperFieldList]} & /@ (Range[n] //. {A___, m_, B___} :> {A,B} /; MemberQ[external[[;;,1]], m]))
			] //.Join[subSum,subSimplifySum] /. SProd[A___][B___] :> SProd[{A}][{B}] //. {
				SProd[{}, A___][{}, B___] :> SProd[A][B],
				SProd[{a___, b_ + c_, d___ }, e___][{f___}, g___] :> SProd[{a, b, d}, e][{f}, g] + SProd[{a, c, d}, e][{f}, g], 
				SProd[{conj[Yuk], A___}, B___][{a_, b_, c_, d___}, e___] :> SProd[{A}, B, conj[SYukContr[a, b, c]]][{d}, e, a, b, c],
				SProd[{Yuk, A___}, B___][{a_, b_, c_, d___}, e___] :> SProd[{A}, B, SYukContr[a, b, c]][{d}, e, a, b, c],
				SProd[{conj[SMass], A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, conj[SMassContr[a, b]]][{c}, d, a, b],
				SProd[{SMass, A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, SMassContr[a, b]][{c}, d, a, b],
				SProd[{conj[STad], A___}, B___][{a_, b___}, c___] :> SProd[{A}, B, conj[STadContr[a]]][{b}, c, a],
				SProd[{STad, A___}, B___][{a_, b___}, c___] :> SProd[{A}, B, STadContr[a]][{b}, c, a],
				SProd[{conj[Delta[a_]], A___}, B___][{b_, c_, d___}, e___] :> KroneckerDelta[a, b] KroneckerDelta[a, c] SProd[{A}, B, delta][{d}, e, b, c],
				SProd[{Delta[a_], A___}, B___][{b_, c_, d___}, e___] :> KroneckerDelta[a, b] KroneckerDelta[a, c] SProd[{A}, B, delta][{d}, e, b, c],
				SProd[{conj[STriLin], A___}, B___][{a_, b_, c_, d___}, e___] :> SProd[{A}, B, conj[STriLinContr[a, b, c]]][{d}, e, a, b, c],
				SProd[{STriLin, A___}, B___][{a_, b_, c_, d___}, e___] :> SProd[{A}, B, STriLinContr[a, b, c]][{d}, e, a, b, c],
				SProd[{conj[SBiLin], A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, conj[SBiLinContr[a, b]]][{c}, d, a, b],
				SProd[{SBiLin, A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, SBiLinContr[a, b]][{c}, d, a, b],
				SProd[{conj[SSMass], A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, conj[SSMassContr[a, b]]][{c}, d, a, b],
				SProd[{SSMass, A___}, B___][{a_, b_, c___}, d___] :> SProd[{A}, B, SSMassContr[a, b]][{c}, d, a, b],
				SProd[{conj[Lambda[i_]], A___}, B___][{a_, b_, c_, d_, e___}, f___] :> SProd[{A}, B, lambda[i, c, d, a, b]][{e}, f, c, d, a, b] KroneckerDelta[a, c] KroneckerDelta[b, d],
				SProd[{Lambda[i_], A___}, B___][{a_, b_, c_, d_, e___}, f___] :> SProd[{A}, B, lambda[i, a, b, c, d]][{e}, f, a, b, c, d] KroneckerDelta[a, c] KroneckerDelta[b, d]
			} // SimplifySProd) //. Join[subSum, subSimplifySum] /. SimplifySum -> Sum]  /.  {
				FProd[A___][B___] :> GProd[1][A][B] Refine[SimplifySum@@Join[
					{
						Expand[(contr@@(FIdx/@Range[n])) (
							(fContr[A]@@(FIdx/@Range[n])) //. {
								fContr[][X___] :> 1,
								fContr[conj[SYukawa[x_]], X___][a_, b_, c_, d___] :> Conjugate[ListSYukawa[[x, 6]][a, b, c]] fContr[X][d],
								fContr[SYukawa[x_], X___][a_, b_, c_, d___] :> ListSYukawa[[x, 6]][a, b, c] fContr[X][d],
								fContr[conj[SMass[x_]], X___][a_, b_, c___] :> Conjugate[ListSMass[[x, 5]][a, b]] fContr[X][c],
								fContr[SMass[x_], X___][a_, b_, c___] :> ListSMass[[x, 5]][a, b] fContr[X][c],
								fContr[conj[STadpole[x_]], X___][a_, b___] :> Conjugate[ListSTadpole[[x, 4]][a]] fContr[X][b],
								fContr[STadpole[x_], X___][a_, b___] :> ListSTadpole[[x, 4]][a] fContr[X][b],
								fContr[delta, X___][a_, b_, c___] :> KroneckerDelta[a,b] fContr[X][c],
								fContr[conj[STriLin[x_]], X___][a_, b_, c_, d___] :> Conjugate[ListSTriLin[[x, 6]][a, b, c]] fContr[X][d],
								fContr[STriLin[x_], X___][a_, b_, c_, d___] :> ListSTriLin[[x, 6]][a, b, c] fContr[X][d],
								fContr[conj[SBiLin[x_]], X___][a_, b_, c___] :> Conjugate[ListSBiLin[[x, 5]][a, b]] fContr[X][c],
								fContr[SBiLin[x_], X___][a_, b_, c___] :> ListSBiLin[[x, 5]][a, b] fContr[X][c],
								fContr[conj[SSMass[x_]], X___][a_, b_, c___] :> Conjugate[ListSSMass[[x, 5]][a, b]] fContr[X][c],
								fContr[SSMass[x_], X___][a_, b_, c___] :> ListSSMass[[x, 5]][a, b] fContr[X][c],
								fContr[lambda[x___], X___][a_, b_, c_, d_, e___] :> KroneckerDelta[a, c] KroneckerDelta[b, d] fContr[X][e]
							} 
						) /. Table[FIdx[external[[i,1]]] -> external[[i,2,2]], {i, 1, Length[external]}]]
					},
					({FIdx[#], 1, ChiralSuperFieldList[[List[B][[#]], 2]]}& /@ (Range[n] //. {Y___, m_, Z___} :> {Y,Z} /; MemberQ[external[[;;,1]], m]))
				] //. Join[subSum,subSimplifySum] /. SimplifySum -> Sum]
			} //. {
				GProd[x_][A___][B___] :> 1 /; (x > NumberOfSubgroups),
				GProd[x_][A___][B___] :> GProd[x+1][A][B] Refine[SimplifySum@@Join[
					{
						Expand[(contr@@((GIdx[#, x])&/@Range[n])) (
							(gContr[A]@@((GIdx[#, x])&/@Range[n])) //. {
								gContr[][X___] :> 1,
								gContr[conj[SYukawa[y_]], X___][a_, b_, c_, d___] :> Conjugate[ListSYukawa[[y, 5, x]][a, b, c]] gContr[X][d],
								gContr[SYukawa[y_], X___][a_, b_, c_, d___] :> ListSYukawa[[y, 5, x]][a, b, c] gContr[X][d],
								gContr[conj[SMass[y_]], X___][a_, b_, c___] :> Conjugate[ListSMass[[y, 4, x]][a, b]] gContr[X][c],
								gContr[SMass[y_], X___][a_, b_, c___] :> ListSMass[[y, 4, x]][a, b] gContr[X][c],
								gContr[conj[STadpole[y_]], X___][a_, b___] :> Conjugate[ListSTadpole[[y, 3, x]][a]] gContr[X][b],
								gContr[STadpole[y_], X___][a_, b___] :> ListSTadpole[[y, 3, x]][a] gContr[X][b],
								gContr[delta, X___][a_, b_, c___] :> KroneckerDelta[a,b] gContr[X][c],
								gContr[conj[STriLin[y_]], X___][a_, b_, c_, d___] :> Conjugate[ListSTriLin[[y, 5, x]][a, b, c]] gContr[X][d],
								gContr[STriLin[y_], X___][a_, b_, c_, d___] :> ListSTriLin[[y, 5, x]][a, b, c] gContr[X][d],
								gContr[conj[SBiLin[y_]], X___][a_, b_, c___] :> Conjugate[ListSBiLin[[y, 4, x]][a, b]] gContr[X][c],
								gContr[SBiLin[y_], X___][a_, b_, c___] :> ListSBiLin[[y, 4, x]][a, b] gContr[X][c],
								gContr[conj[SSMass[y_]], X___][a_, b_, c___] :> Conjugate[ListSSMass[[y, 4, x]][a, b]] gContr[X][c],
								gContr[SSMass[y_], X___][a_, b_, c___] :> ListSSMass[[y, 4, x]][a, b] gContr[X][c],
								gContr[lambda[y_, pa_, pb_, pc_, pd_], X___][a_, b_, c_, d_, e___] :> \[CapitalLambda][y][pa, pb, pc, pd][a, b, c, d] gContr[X][e] /; (x == y),
								gContr[lambda[y_, p___], X___][a_, b_, c_, d_, e___] :> KroneckerDelta[a, c] KroneckerDelta[b, d] gContr[X][e]

							} 
						) /. Table[GIdx[external[[i,1]], x] -> external[[i,2,3,x]], {i, 1, Length[external]}]]
					},
					({GIdx[#,x], 1, SMultiplicity[List[B][[#]], x]}& /@ (Range[n] //. {Y___, m_, Z___} :> {Y,Z} /; MemberQ[external[[;;,1]], m]))
				]//. Join[subSum,subSimplifySum] /. SimplifySum -> Sum]
			}
		];

		(* Replacement for Lambda functions *)
		(*  Generator of different superfields *)
		\[CapitalLambda][g_][pa_, pb_, pc_, pd_][a_, b_, c_, d_] := 0 /; (pa =!= pc  || pb =!= pd);
		(*  non-abelian gauge singlet *)
		\[CapitalLambda][g_][pa_, pb_, pa_, pb_][a_, b_, c_, d_] := 0 /; (ListGauge[[g, 3]] =!= 1 && ( ChiralSuperFieldList[[pa, 3, g]] === 1 || ChiralSuperFieldList[[pb, 3, g]] === 1));
		(*  SU(N) all fields in fundamental representation *)
		\[CapitalLambda][g_][pa_, pb_, pa_, pb_][a_, b_, c_, d_] := 1/2 ( KroneckerDelta[a, d] KroneckerDelta[b, c]  - 1/ListGauge[[g, 3]] KroneckerDelta[a, c] KroneckerDelta[b, d]) /; (ListGauge[[g, 2]] === SU && ListGauge[[g, 3]] === ChiralSuperFieldList[[pa, 3, g]] && ListGauge[[g, 3]] === ChiralSuperFieldList[[pb, 3, g]]);
		(*  SO(N) all fields in fundamental representation *)
		\[CapitalLambda][g_][pa_, pb_, pa_, pb_][a_, b_, c_, d_] := ( KroneckerDelta[a, d] KroneckerDelta[b, c]  - KroneckerDelta[a, b] KroneckerDelta[c, d]) /; (ListGauge[[g, 2]] === SO && ListGauge[[g, 3]] === ChiralSuperFieldList[[pa, 3, g]] && ListGauge[[g, 3]] === ChiralSuperFieldList[[pb, 3, g]]);
		(*  U(1) subgroup *)
		\[CapitalLambda][g_][pa_, pb_, pa_, pb_][a_, b_, c_, d_] := KroneckerDelta[a, c] KroneckerDelta[b, d] ChiralSuperFieldList[[pa, 3, g]] ChiralSuperFieldList[[pb, 3, g]] /; (ListGauge[[g, 2]] === U && ListGauge[[g, 3]] === 1 );
		(*  unknown case *)
		\[CapitalLambda][g_][pa_, pb_, pa_, pb_][a_, b_, c_, d_] := \[CapitalLambda][ListGauge[[g, 1]], ChiralSuperFieldList[[pa, 1]], ChiralSuperFieldList[[pb, 1]], ChiralSuperFieldList[[pa, 1]], ChiralSuperFieldList[[pb, 1]]][a, b, c, d];
		
		
		(* workaround a mathematica bug *)
		ListPosition[A_, B___] := Position[A//. {{} -> $EMPTYLIST}, B];

		(* function to simplify traces etc *)
		SimplifyProduct[term_] := (ContractSum2[term //. subProd //.{
			conj[conj[a_]] :> a,
			tr[adj[a_], b__] :> tr[b, adj[a]],
			(A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[G___, c_, adj[d_], F___, C___, a_, adj[b_]]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F],
			(A_ tr[C___, a_, adj[b_], G___, c_, adj[d_], F___] + B_ tr[c_, adj[d_], F___, C___, a_, adj[b_], G___]) :> (A+B)tr[C, a, adj[b], G, c, adj[d], F],
			tr[conj[A_], adj[conj[B_]]]:>conj[tr[A,adj[B]]],
			tr[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]]]:>conj[tr[A,adj[B],C,adj[E]]],
			tr[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]], conj[F_], adj[conj[G_]]]:>conj[tr[A,adj[B],C,adj[E],F,adj[G]]],
			prod[conj[A_], adj[conj[B_]]][i_,j_]:>conj[prod[A,adj[B]][i,j]],
			prod[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]]][i_,j_]:>conj[prod[A,adj[B],C,adj[E]][i,j]],
			prod[conj[A_], adj[conj[B_]], conj[C_], adj[conj[E_]], conj[F_], adj[conj[G_]]][i_,j_]:>conj[tr[A,adj[B],C,adj[E],F,adj[G]][i,j]],
			tr[A___, adj[B_], C___] :> tr[A, adj[B], C],
			prod[A___, adj[B_], C___] :> prod[A, adj[B], C],
			adj[conj[A_[i_,j_]]] :> A[j,i],
			adj[A_[i_,j_]] :> conj[A[j,i]],
			adj[conj[A_]] :> A, adj[A_]:>conj[A]
		} //. {Sum[A_, B___]:>SimplifySum[Expand[A],B]}]
		);
		
		(* Define Sum that resolves all KroneckerDelta[__] and Generators before it does the summation *)
		subSum := {
			A_ SimplifySum[B_, C___] :> SimplifySum[A B, C],
			SimplifySum[A_ + B_, C___] :> SimplifySum[A, C] + SimplifySum[B, C],
			SimplifySum[D_ (A_ + B_), C___] :> SimplifySum[D A, C] + SimplifySum[D B, C],
			SimplifySum[SimplifySum[A_, B___], C___] :> SimplifySum[A, B, C],
			SimplifySum[A_, SS1___, {aa_, 1, 1}, SS2___] :> SimplifySum[(A /. {aa->1}), SS1, SS2],
			Conjugate[KroneckerDelta[A___]] :> KroneckerDelta[A],
			Conjugate[B_ KroneckerDelta[A___]] :> Conjugate[B] KroneckerDelta[A],
			SimplifySum[A_ KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			SimplifySum[A_ KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			Power[KroneckerDelta[A___], a_] :> KroneckerDelta[A],
			Conjugate[Generator[A___][a_, i_, j_]] :> Generator[A][a, j, i],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3], 
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3], 
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C T2[A]KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[T2[A] KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[A_] :> A,
			SimplifySum[] :> 0
		};
		
		(* like subSum, but with more advanced simplifications to be utilized in SimplifyProduct *)
		subSum2 := {
			A_ SimplifySum[B_, C___] :> SimplifySum[A B, C],
			SimplifySum[A_ + B_, C___] :> SimplifySum[A, C] + SimplifySum[B, C],
			SimplifySum[D_ (A_ + B_), C___] :> SimplifySum[D A, C] + SimplifySum[D B, C],
			SimplifySum[SimplifySum[A_, B___], C___] :> SimplifySum[A, B, C],
			SimplifySum[A_, SS1___, {aa_, 1, 1}, SS2___] :> SimplifySum[(A /. {aa->1}), SS1, SS2],
			Conjugate[KroneckerDelta[A___]] :> KroneckerDelta[A],
			Conjugate[B_ KroneckerDelta[A___]] :> Conjugate[B] KroneckerDelta[A],
			SimplifySum[A_ KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[aa_, bb_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			SimplifySum[A_ KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[A //. aa->bb , SS1, SS2],
			SimplifySum[KroneckerDelta[bb_, aa_], SS1___, {aa_, 1, cc_}, SS2___] :> SimplifySum[1 , SS1, SS2],
			Power[KroneckerDelta[A___], a_] :> KroneckerDelta[A],
			Conjugate[Generator[A___][a_, i_, j_]] :> Generator[A][a, j, i],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3], 
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3], 
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][a_, j_, k_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___] :> SimplifySum[C2[A] KroneckerDelta[i, k], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[C T2[A]KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[Generator[A___][a_, i_, j_] Generator[A___][b_, j_, i_], SS1___, {i_, 1, ii_}, SS2___, {j_, 1, jj_}, SS3___] :> SimplifySum[T2[A] KroneckerDelta[a, b], SS1, SS2, SS3],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {k_, 1, kk_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {j_, 1, jj_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {k_, 1, kk_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {j_, 1, jj_}, SS3___, {a_, 1, aa_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {k_, 1, kk_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {k_, 1, kk_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {a_, 1, aa_}, SS2___, {j_, 1, jj_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {a_, 1, aa_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[C (C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {j_, 1, jj_}, SS2___, {a_, 1, aa_}, SS3___, {k_, 1, kk_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[Generator[A_, B___][a_, i_, j_] Generator[A_, B___][b_, j_, k_] Generator[A_, B___][a_, k_, l_], SS1___, {k_, 1, kk_}, SS2___, {a_, 1, aa_}, SS3___, {j_, 1, jj_}, SS4___] :> SimplifySum[(C2[A, B] - 1/2 C2[B]) Generator[A, B][b, i, l], SS1, SS2, SS3, SS4],
			SimplifySum[C_ Conjugate[B_ \[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[C Conjugate[B] \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[C_ Conjugate[\[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[C \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[Conjugate[B_ \[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[Conjugate[B] \[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[Conjugate[\[CapitalLambda][g_, p1_, p2_, p3_, p4_][i1_, i2_, i3_, i4_]], SS1___] :> SimplifySum[\[CapitalLambda][g, p3, p4, p1, p2][i3, i4, i1, i2], SS1],
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][b_, a_, a_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, ferm_, ferm_, conj[ferm_], conj[ferm_]][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], conj[ferm_], ferm_, ferm_][a_, b_, c_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, ferm_, conj[ferm_], conj[ferm_], ferm_][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][b_, c_, a_, a_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[C_ \[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[\[CapitalLambda][g_, conj[ferm_], ferm_, ferm_, conj[ferm_]][a_, a_, b_, c_], SS1___, {a_, 1, aa_}, SS2___] :> SimplifySum[C2[ferm, g] KroneckerDelta[b,c], SS1, SS2],
			SimplifySum[A_] :> A,
			SimplifySum[] :> 0
		};
		
		
		ContractSum[A_, B___] := Block[
			{res},
			res = SimplifySum[Expand[A],B]//.subSum;
			Return[Refine[res/.SimplifySum -> Sum]];
		];
		
		ContractSum2[A_, B___] := Block[
			{res},
			res = SimplifySum[Expand[A],B]//.Join[subSum2,subSimplifySum];
			Return[Refine[res/.SimplifySum -> Sum]];
		];
		
		(* Error Messages *)
		Gauge::RepMismatch = "Representation list does not match number of subgroups";
		Gauge::NAN = "Number of subgroups is corrupted";
		Gauge::Full = "Number of gauge subgroups exceeds initial definition";
		Gauge::RepInvalid = "Invalid input for gauge indices";
		Gauge::NoMem = "Gauge is not part of the specified group";
		Gen::RepInvalid = "Invalid input for generation indices";
		Yukawa::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Yukawa::UnknownParticle = "Undefined particle in Yukawa sector";
		Mass::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Mass::UnknownParticle = "Undefined particle in mass term";
		Tadpole::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Tadpole::UnknownParticle = "Undefined particle";
		Quartic::ContractionError = "Number of gauge contractions does not match number of subgroups";
		Scalar::UnknownParticle = "Undefined Scalar field";
		
		Reset[];
	End[];
EndPackage[];
