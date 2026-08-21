# Formaliga plano de Ript

[English](../../en/reference/BLUEPRINT.md) · [简体中文](../../zh-CN/reference/BLUEPRINT.md) ·
[日本語](../../ja/reference/BLUEPRINT.md) · [Esperanto](BLUEPRINT.md)

La plano registras nur realigan staton kontrolitan de la Lean-kerno. La solaj
statusoj estas `DEFINED`, `STATEMENT_FORMALIZED`, `PROVED`, `BLOCKED` kaj
`OPEN_RESEARCH`. La [maŝina kanona plano](../../../BLUEPRINT.md) konservas la
plenan Lean-tipon, dependecojn, supozojn kaj fonton de ĉiu deklaro; ĉi tiu
traduko konservas la samajn fazlimojn kaj teoremfamiliojn.

## Esplorcelo

Konstrui komputeblan, maŝine kontroleblan, univalentan kaj pli-alt-kategorian
teorion de rimed-limigitaj informprocezoj, kun klasika probablo, kvantumaj
procezoj, kaŭzaj modeloj, komputado, semantika informo kaj termodinamiko kiel
malsamaj modeloj ligitaj per reprezentaj kaj kompletecaj teoremoj. Loka
`PROVED`-statuso ne signifas, ke la tuta celo estas finita.

## Ĉefa dependeca direkto

```text
Rimeda algebro → Kostita procezo → Buĝetoj/filtradoj/rimedŝanĝoj
      ↓
Seria sintakso → Interpreto → Valideco → Termmodelo → Relativa kompleteco/strikta komenceco/voja reprezento
      ↓
Monoida sintakso → Paralela kosto → Semantiko → Libera komenceco
      ↓
Funkciaj / probablaj / decidaj / komputaj / kaŭzaj / termikaj / kvantumaj modeloj
      ↓
Modelbikategorio → Heterogena totala bikategorio → Lokalizado
      ↓
Interna univalenta sintakso → Grupoido/kvociento/skeleto → Yoneda → Nervo → Klasifika diagramo
```

Komuna monoida sintakso povas puŝi nur siajn kostojn laŭ `φ : R →+o S`.
Dratoj kaj generatoroj restas samaj, esprimtraduko estas inversebla, heterogena
interpreto ekvivalentas al ordinara puŝita interpreto, kaj la libera modelo
ekzakte realigas la tradukitan buĝeton.

## Fazaj statoj

| Fazo | Amplekso | Stato |
| --- | --- | --- |
| 0 | Medio, projekto, dokumentaro, CI kaj auditbazo | `PROVED` |
| 1 | Seria rimed-proceza vertikala tranĉo | `PROVED` |
| 1 (finia determinisma) | Kartezia tensoro, kopio/forĵeto, kaŭzeco, Bulea atesto | `PROVED` |
| 1 (reprezento) | Kostoj kaj atingitaj buĝetfiltradoj kun ekzaktaj revenoj | `PROVED` |
| 2 | Tensoro, simetrio, paralelaj rimedoj kaj libera universala levo | `PROVED` |
| 2 (ĝenerala seria reprezento) | Generatoraj vojoj, eksplicita ekvivalento de la kvocienta termkategorio kun la vojkategorio, ekzakta libera kosto, semantika vojbildo kaj vojfidela kompleteco | `PROVED` |
| 2 (seria komenceco) | Klasifikaj ekvivalentoj inter interpretoj kaj liber-fontaj rimedfunktoroj; kuntireblaj strikt-etendaj tipoj ankaŭ laŭ `φ : R →+o S` | `PROVED` |
| 3–5 | Finia stokastiko, distribua Kleisli kaj Mathlib `Stoch`-reprezento | `PROVED` |
| 6 | Blackwell-ordo, finia risko, plena inverso, racionala apartigo, semantika valoro kaj tut-taskaj ordo/profila kompleteco | `PROVED` |
| 7 (komputado) | Plurdimensia totala kaj `Option`-parta komputado | `PROVED` |
| 7 (hazardigita komputado) | Ekzaktaj stokastaj kernoj, kvar-dimensiaj rimedoj, ruleblaj buĝetoj, ekzakta seria/paralela adicio kaj plena simetria monoida strukturo | `PROVED` |
| 7 (kaŭza) | Finiaj DAG-oj, komunaj distribuoj, fiks-DAG-aj molaj/stokastaj/malmolaj intervenoj, reduktita last-write-wins normformo, ekzakta modela/kanala reprezento kaj kompleteco | `PROVED` |
| 8 | Finiaj ekvilibroj, interna Gibbs-konserva kanalbildo kaj unika levo, Gibbs-klasifiko, libera energio, korelacio, Landauer | `PROVED` |
| 9 | Kraus-kanaloj/operacioj, normaligitaj instrumentoj, dependa bind kaj Born-ĉenleĝo, unuaklasa rekursia instrumentarbo, kanonaj dependaj historioj, ekzakta branĉreprezento, komputeblaj historikostoj/arbobuĝeto, registra reprezento kaj plena simetria monoida strukturo | `PROVED` |
| 10 | Fiks-rimeda modelbikategorio, 2-ĉeloj, kohereco kaj kost-ekzakta ekvivalento | `PROVED` |
| 10 (heterogenaj rimedoj) | Reindeksado, heterogenaj fortaj modelmapoj kaj buĝettransporto | `PROVED` |
| 10 (heterogena sintakso) | Inverseblaj esprimaj/pruvaj tradukoj, pruvteoria konservemo, heterogena valideco, rekta forta simetria rimedŝanĝa libera levo, kuntirebla strikta etendo kaj ekzaktaj buĝetoj | `PROVED` |
| 10 (komuna ses-modela tranĉo) | Unu unu-kosta Bulea turno kun probabla, kvantuma, kaŭza, komputa, semantika kaj termika interpretoj | `PROVED` |
| 10 (ses-modela kompona tranĉo) | Tri interfacoj kaj du turnoj kontrolitaj per probabla komponado, Pauli-X, trinoda kaŭza ĉeno, rimedadicio, semantika posttraktado kaj ferma termika protokolo | `PROVED` |
| 10 (ses-modela lineara kompleteco) | Komputeblaj normvojoj, unika normaligo, maldika termmodelo, unu-elementa bildreprezento, rimedtraduka konservemo kaj egalreflektado | `PROVED` |
| 10 (ses-modela operacia viŝado) | Du-koordinata expose–erase kun klasika konstanto, kvantuma reset, kaŭza mekanism-anstataŭigo, komputa kosto, semantika valorperdo kaj Landauer-saturiĝo | `PROVED` |
| 10 (ses-modela nemaldika kompleteco) | Kvar-rimeda diamanta sintakso, du formale malsamaj vojoj, branĉ-konserva normaligo, ekzakta du-elementa bildo, voja apartigo kaj ses-modela kompleteco | `PROVED` |
| 10 (ses-modela paralela tranĉo) | Ses-modela kontrolo de komuna simetria monoida `flip ⊗ flip`; la ses kanonaj heterogenaj levoj estas 1-ĉeloj el unu komuna sintaksa objekto en la totala rimed-modela bikategorio | `PROVED` |
| 10 (ses-modela ekzakta bruo) | Kvaron-transira BSC kiel probablo, hazard-unueca kvantumo, brua kaŭzeco, kvar-rimeda hazardigita komputado, semantiko kaj Gibbs-konservo; ekzakta kongruo, kohera apartigo, semantika valoro kaj ses liberaj levoj | `PROVED` |
| 10 (ses-modela adapta branĉarbo) | Fiksprofunda duuma rezult-dependa generatora elekto, pozitiv-historia normformo, ekzaktaj vojkostoj/plejmalbona buĝeto, registrita-kanala reprezento kaj observa kompleteco, kun duprofunda ses-modela realigo | `PROVED` |
| 10 (dependa finia branĉado) | Vari-profundaj generator-dependaj arbitraj finiaj rezultoj, dependaj Sigma-historioj, ekzaktaj alto/vojkosto/buĝeto, reprezento kaj observa kompleteco laŭ eksplicitaj historiaj ekvivalentoj, konservema duuma enmeto | `PROVED` |
| 10 (libera dependa branĉalgebro) | Kategorio de branĉalgebroj, komenca arbalgebro, unika fold, eksplicita valida kaj absolute kompleta kongrueco, asocia unuhava foligreftado kaj subadiciaj alto/buĝeto-fold-oj | `PROVED` |
| 10 (simetria monoida branĉalgebro) | Elektitaj terminalo/duumaj produktoj, kartezia simetria monoida strukturo kun plena kohero/kopio/forĵeto, komponanta produkt-fold, dumodela samtempa egaleco kaj komuna termmodela kompleteco | `PROVED` |
| 10 (arb-nivela sendependa paralela branĉado) | Eksplicitaj heterogenaj du lenoj, parigitaj normaligitaj historioj/statoj, ekzakta kanalerfaktorado, rimedadicio, lena simetrio, komun-faza greftado, strikta tensor–seria interŝanĝo kaj paralela observa kompleteco | `PROVED` |
| 10 (totala bikategorio) | Pakitaj rimedalgebroj, heterogenaj 1-/2-ĉeloj, interŝanĝo, kvinangulo, triangulo | `PROVED` |
| 12 (total-modela simplicia ponto) | Kan-a strikta-Segal objekt-ekvivalenta kerno, ekzakta interna-ekvivalentklasa/identeca-eĝa korespondo, plenaj lokaj mapnervoj retenantaj neinversigeblajn 2-ĉelojn, kohera tutmonda Duskin 3-skeleto, tutdimensia koordinata duonsimplicia nervo kaj indiĝena plena Duskin-nervo de strikte unuigaj malstriktaj fin-ordinalaj diagramoj kun ĉiuj degeneroj | `PROVED` |
| 10 (ordinara lokalizado) | Kost-ekzakta lokalizado de la modela homotopia 1-kategorio | `PROVED` |
| 11 | Senaksioma profunda sintakso, kvocienta grupoido kaj interna univalenteco | `PROVED` |
| 12 (tranĉita/antaŭgarba/grupoida) | Objekta kompletigo, skeleto, Yoneda kaj ordinara lokalizado | `PROVED` |
| 12 (simplicia) | Kan, strikta Segal, kvazaŭkategorio, 2-koskeleto kaj homotopia reakiro | `PROVED` |
| 12 (klasifika diagramo) | Rezk-diagramo, ekstera Segal, kongruaj limoj kaj fibradoj | `PROVED` |
| 12 (pli alta lokaliza specifo) | Markinversigo, pseŭdofunktora antaŭkompono, lokaj ekvivalentoj, irantaj testoj | `PROVED` |
| 12 (pli alta lokaliza konstruo) | Lokaliza pseŭdofunktoro por la plena rimed-proceza bikategorio; dimensio-laŭa ekvivalento inter indiĝenaj normal-malstriktaj kaj koordinataj Duskin-simplaĵoj; complete-Segal 2-spaca kunmeto; kaj la koncernaj malforta ekvivalento kaj universala komparo | `OPEN_RESEARCH` |

## Ĉefaj teoremfamilioj

- Rimedoj: buĝetitaj identecoj/komponado, filtrado-kostaj rondiroj kaj reindeksado.
- `SequentialNormalForm`: termkategoria–vojkategoria ekvivalento, ekzakta kostkonservo, vojbildo kaj vojfidela kompleteco por arbitraj seriaj signaturoj.
- `SequentialFree/ResourceChangingSequentialFree`: klasifiko de interpretoj per liber-fontaj rimedfunktoroj, kuntireblaj strikt-etendaj tipoj, liberaj levoj kaj kostlimoj.
- Sintakso: `eval_cost_le`, seria/monoida valideco, relativa kompleteco kaj unikeco de libera levo.
- Heterogena sintakso: reprezenta ekvivalento, tradukita taksa limo kaj ekzakta libera buĝeto.
- Ses modeloj: modelspecifaj Buleaj turnoj, komputa rimedtraduko kaj `sixModelFlipAgreement`.
- Kompona tranĉo: du turnoj restarigas identecon en `sixModelCompositionAgreement`.
- `CompositionalBitCompleteness`: normformoj, ekzakta bildo kaj `sixModelSemanticCompleteness`.
- Operacia viŝado: ses-modelaj reset, interveno, valorperdo kaj `sixModelErasureAgreement`.
- `DiamondBitTheory/Realizations`: nemaldika ekzakta bildo, ses-modela voja apartigo, semantika kompleteco kaj ses kanonaj heterogenaj liberaj levoj.
- `ParallelBitRealizations/HigherModels`: ses-modela paralela konduto, plena Kraus-kvantuma celo, tensoraj Pauli-X-kanaloj sur arbitraj produktaj densecmatricoj, ekzakta komput-rimeda adicio kaj total-bikategoriaj 1-ĉeloj kun kontrolitaj rimedmapoj.
- `QubitInstrument/InstrumentSyntax`: plus-mezuro kaj retrokuplo, unuaklasa rekursia arbo kun tri probabloj `1/2, 1/2, 0` kaj buĝeto `2`, historia branĉreprezento kaj unu-/du-unua rimeda libera levo.
- `NoisyBitRealizations`: ses-modela komuna `3/4–1/4` brua limo, apartigo de plus-koheron konservanta hazard-unueca kvantumo disde mezur–preparo, ekzaktaj komputrimedoj kaj semantika risko/valoro.
- `Syntax.Branching/AdaptiveNoiseRealizations`: ruleblaj historioj, pozitivaj branĉtabelaj normformoj, ekzaktaj kostoj, reprezento kaj observa kompleteco por arbitraj fiksprofundaj duumaj arboj; plurgeneratora ses-modela ekzemplo kun kohera kaj kompleteca apartigo.
- `Syntax.DependentBranching/Examples.DependentBranching`: vari-profundaj arboj kun generator-specifaj finiaj rezulttipoj, eksplicitaj historiaj ekvivalentoj, registrita-tabela reprezento/kompleteco kaj konservema duuma enmeto; la `Bool`/`Fin 3`-ekzemplo havas kvin diverslongajn historiojn.
- `Syntax.DependentBranching.Free`: kategorio de branĉalgebroj kaj homomorfioj, komenca arbalgebro, unika libera interpreto, validaj/kompletaj ekvacioj en ĉiuj algebroj, seria grefta monoido kaj nombraj alto/buĝeto-fold-oj.
- `Syntax.DependentBranching.Monoidal`: elektitaj finiaj produktoj kaj kartezia simetria monoida kohero de modelalgebroj, produkt-fold kiu ekzakte parigas du modelinterpretojn, kaj komuna termmodela kompleteco.
- `Syntax.DependentBranching.Parallel`: arb-nivelaj eksplicitaj du lenoj, sendependa stokasta kanalfaktorado, interŝanĝa simetrio, rimedadicio, komun-faza seria greftado, strikta interŝanĝo kaj paralela kompleteco.
- Probablo kaj decido: `FiniteStochastic`, Kleisli/`Stoch`, Blackwell-inverso,
  racionala apartigo, tut-taska ekzakta nombrovalora profila kompleteco kaj
  unu-taska nekompleteca atestanto.
- Komputado kaj kaŭzeco: plurdimensiaj limoj, parta komputado, DAG-normaligo
  kaj reduktitaj molaj/stokastaj/malmolaj intervenaj normformoj kun
  reprezento/kompleteco.
- Termodinamiko: interna bildo kaj unika levo de Gibbs-konservaj kanaloj, KL,
  libera energio, korelacio, Landauer kaj ban/bateriaj atestantoj.
- Kvantumo: Kraus-pozitiveco kaj spuro-konservo, operacioj kaj finiaj instrumentoj, normaligitaj Born-probabloj kaj postaj statoj, seriaj/paralelaj instrumentleĝoj, klasik-registra kanalreprezento, plena simetria monoida kohero, kompleta pozitiveco kaj klasika enigo.
- Pli altaj tavoloj: fiksaj kaj totalaj bikategorioj, kost-ekzaktaj ekvivalentoj kaj lokalizaj testoj.
- Univalenteco: interna identeco, objekta kompletigo, Yoneda, Kan-nervo, Segal kaj klasifika diagramo.

Por la ekzakta Lean-tipo kaj `Classical.choice`-limo de ĉiu deklaro, uzu la
[plenan anglan planon](../../en/reference/BLUEPRINT.md) aŭ la
[maŝinan kanonan registron](../../../BLUEPRINT.md).

## Nefinita limo

Restas nepruvitaj: skaleblaj modelspecifaj bildkarakterizoj por molaj,
heterogen-portantaj, graf-ŝanĝaj aŭ politik-dependaj kaŭzaj intervenoj,
rimed-limigitaj semantikaj profiloj aŭ pli riĉaj/senfinaj tasklingvoj, kaj
energi-rezolvaj termik-operaciaj dilatoj; veraj
intermodelaj komparoj; kaj universala
interna-univalenta aŭ norma complete-Segal-lokalizado de la plena
rimed-proceza bikategorio. Neniu el tiuj estas kaŝita kiel Lean-aksiomo aŭ
pruvita lokokupilo.
