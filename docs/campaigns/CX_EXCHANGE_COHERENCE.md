# CX — Intercambios causales, coherencias y realizaciones

Fecha: 2026-09-28.
Estado: PLANIFICACION ESPECIFICADA; implementacion y acreditacion nuevas PENDIENTES.
Base documental revisada: CausalGeometry/main, 3a90c3a4069cab6a84836cbc54ff1b99225a77ad.

## 0. Mandato y lugar en el programa

CX desarrolla la ampliacion solicitada: transformaciones tipadas entre historias sin imponer universalmente simetria, trenzado, invertibilidad ni coherencia de Yang–Baxter. Conserva y realiza los sectores donde esas leyes son verdaderas. No reemplaza la campaña causal original, la aritmetica causal, la restriccion correlativa, CA21/CA22, ni las rutas de ECIA. No pertenece a RenormCore, FGA o al motivo generativo dinamico.

La motivacion ya estaba en CA-13.15 (extension causal trenzada) y CA-13.16 (realizacion ribbon). CX hace explicito el fundamento mas general que esas filas necesitan y sus conexiones con CA02/03, CA09/10, CA14/15, CA17/18 y CA21–25. La obligacion trenzada original sigue siendo obligatoria: generalizar su ambiente no la elimina.

Hay dos frentes simultaneos, con dependencias LOCALES:

* FUENTE: construir la matematica causal y sus modelos intrinsecos, dependiendo solamente de mathlib y del nucleo causal.
* REALIZACION: interpretar cada productor disponible en estructuras concretas de ECIA/GenContinuum; demostrar preservacion, perdida y comparaciones.

Un productor causal se acredita con sus propios teoremas, consumidores internos, controles y auditorias. No queda bloqueado por una realizacion ECIA aun abierta. Una realizacion necesita los productores que usa, no la terminacion de todo CX. Que un destino sea trenzado no demuestra que la fuente general lo fuera.

El registro historico mantiene sus 636 filas. CX introduce 96 subobligaciones de planificacion CX00.01–CX11.08, NO 96 teoremas acreditados ni una renumeracion del ledger Lean. Su cruce con las filas existentes figura en CX_OBLIGATIONS.md. Una futura incorporacion al enumerado ejecutable debe ser una migracion explicita, sin doble conteo.

Documentos normativos de esta ampliacion:

* CX_EXCHANGE_COHERENCE.md: especificacion matematica y arquitectura.
* CX_OBLIGATIONS.md: 96 subobligaciones, dependencias y salidas.
* CX_COMPLEXITY_AND_VALIDATION.md: recursos, controles y evidencia.
* CX_ECIA_REALIZATIONS.md: programa paralelo de consumidores.

Esta entrega modifica planificacion, no archivos Lean, dependencias, pins ni runners; no crea ramas, merges ni workflows.

## 1. Que objeto se conserva

El origen sigue siendo EventSystem. Las configuraciones, caminos, historias, diarios y numeros causales permanecen derivados. No se introduce un espacio fisico de hebras ni una memoria de estado como nueva primitiva ontologica.

Fijadas fronteras A,B, se conserva una presentacion de historias H(A,B). Un intercambio elemental es un dato

    alpha : ExchangeStep h k

entre historias admitidas con la misma frontera, salvo que un comparador de fronteras sea parte explicita del tipo. La habilitacion y la compatibilidad causal son requisitos, no consecuencias del nombre exchange.

Hay que distinguir desde el principio:

1. intercambio cronologico entre ejecuciones de eventos concurrentes;
2. intercambio de factores del producto paralelo de procesos;
3. transformacion de una factorizacion por movimientos de Hurwitz;
4. reescrituras adicionales que preserven una semantica declarada.

No se identifica ninguna pareja por semejanza grafica. Un grupo B_n de rango fijo solo puede aparecer tras construir un dominio de n componentes, generadores y relaciones. Creacion, fusion, colores y fronteras variables requieren categorias o grupoides tipados, no una identificacion artificial con un unico B_n.

## 2. Niveles de igualdad y de informacion

Se mantendran separados:

* igualdad de configuraciones finales;
* igualdad de historias o de su presentacion;
* existencia de una transformacion h -> k;
* igualdad entre dos transformaciones P,Q : h -> k;
* existencia de una celda superior Theta : P ==> Q;
* igualdad tras una realizacion o tras un cociente declarado.

Igualdad de extremos no identifica rutas. Una celda superior no se convierte silenciosamente en igualdad de sus extremos. Una observacion numerica igual tampoco implica igualdad de rutas.

En Lean, los datos de ExchangeStep, ExchangePath y las celdas superiores cuya identidad interese deben vivir en Type. Los predicados de buena formacion, leyes y existencia pueden vivir en Prop. La irrelevancia de pruebas de Prop hace incorrecto usar dos pruebas de h = k como si fueran dos intercambios distinguibles [R6]. Una presentacion explicita por generadores y relaciones es el camino previsto; no se supone que Lean tenga un tipo inductivo superior nativo para esta construccion.

## 3. Construccion minima y propiedad universal

### 3.1 Intercambios dependientes de contexto

Reutilizar CausalPath y los certificados de habilitacion/concurrencia. Para u; e; f; v -> u; f; e; v, ambos lados deben existir y sus fronteras deben coincidir mediante la igualdad ya demostrada por el diamante. Los contextos no se borran. La repeticion de una etiqueta no autoriza repetir una ocurrencia: EventSystem distingue eventos y ejecutar una ocurrencia la consume.

La familia de pasos forma un quiver sobre historias. Su categoria libre de caminos compone certificados, no solo pares de extremos. Reutilizar Quiver.Path y Paths cuando existan en el mathlib fijado, mediante una auditoria de firmas antes de programar; la documentacion de upstream no sustituye la verificacion del pin [R7].

Para cada interpretacion de pasos en una categoria D, construir la extension a caminos, probar identidad y composicion, y demostrar unicidad. No basta una estructura con un campo llamado universal.

### 3.2 Contextos y composicion de diarios

La accion de contextos sobre pasos y caminos debe preservar habilitacion y fronteras. La composicion horizontal de transformaciones depende del productor real de composicion de diarios. Si ese productor falta, CX registra la dependencia exacta de CA03: no la reemplaza por un parametro sin reconocerlo.

Un sistema contextual o sesquicategorial no se llama bicategoria hasta demostrar los axiomas necesarios. En particular, intercambio horizontal/vertical, pentagono, triangulo, naturalidad y hexagonos son leyes distintas. Tampoco se aplana composicion secuencial y producto paralelo: un colapso de dos composiciones con la misma unidad e intercambio puede introducir conmutatividad no pretendida.

### 3.3 Congruencia de coherencia

Una politica K selecciona pares de rutas paralelas y sus instancias contextuales. Construir la menor congruencia que los contiene y es estable por composicion. El cociente HEx/K debe venir con factor universal:

    F factoriza por HEx/K  <=>  F respeta todos los generadores de K.

Se requiere demostrar que respetar generadores implica respetar toda la congruencia, no suponerlo como otro campo. Para K subset L, construir HEx/K -> HEx/L. Estas flechas ordenan PERDIDA de informacion. No son automaticamente inclusiones fieles.

No se promete un procedimiento de decision universal para la igualdad en presentaciones arbitrarias. Una busqueda acotada que no encuentre prueba devuelve INCONCLUSO, nunca desigualdad.

## 4. Arquitectura de sectores: un diagrama, no una cadena

La capa base no presupone naturalidad global, intercambio para todos los pares, inversos, conmutatividad lejana, Yang–Baxter, involutividad o existencia de 3-celdas.

Las especializaciones separan:

| Sector | Hipotesis adicionales | Lo que NO se infiere |
|---|---|---|
| Reescritura dirigida | Pasos y composicion bien tipados | Inversos o trenzas |
| Intercambio reversible | Inversos de los pasos declarados | Yang–Baxter o simetria |
| Twin | Involutividad y conmutatividad lejana | Relacion ternaria de trenza |
| Yang–Baxter no invertible | Operadores coherentes con YB | Accion del grupo B_n |
| Trenzado | Isomorfismos naturales y hexagonos | Involutividad |
| Simetrico | Trenzado e intercambio doble identidad | Fidelidad de cualquier realizacion |
| Coboundary/cactus | Conmutador involutivo y coherencia cactus | Hexagonos de trenzado |
| Coherencia superior | Comparadores entre rutas y sus leyes | Igualdad estricta de rutas |

Para acciones sobre potencias de un objeto, YB y conmutatividad lejana construyen una accion de B_n^+; invertibilidad permite extenderla a B_n. Un operador YB aislado sobre un objeto no equipa por si solo toda una categoria de un trenzado natural [R3].

Los twin groups tienen generadores involutivos y conmutatividad lejana sin la relacion adyacente de trenza [R2]. Las categorias coboundary tienen otra coherencia y dan acciones cactus [R1]. No se afirma que todos esos sectores se incluyan unos en otros. Las comparaciones entre presentaciones son obligaciones separadas.

Recuperar el sector simetrico historico mediante un comparador probado. No basta enviar cada generador a una transposicion; hay que probar exactamente que relaciones presenta ese cociente en el dominio causal declarado.

## 5. Defectos y transporte: resultados objetivo

Sean P,Q : h -> k las dos rutas ternarias admitidas:

    P = sigma_1 sigma_2 sigma_1
    Q = sigma_2 sigma_1 sigma_2.

La notacion omite solo los contextos y transportes de tipo ya fijados. La convencion de composicion se debe documentar y probar en cada implementacion.

### 5.1 Defecto reversible

Si P,Q son isomorfismos, definir Omega(P,Q)=Q^{-1} o P, automorfismo de h. Demostrar:

    Omega(P,Q)=id <=> P=Q.

Para isomorfismos de fronteras a:h'->h y b:k->k', las rutas b P a y b Q a tienen defecto

    Omega(b P a,b Q a)=a^{-1} Omega(P,Q) a.

Por tanto la igualdad a identidad es invariante de cambio de presentacion; el elemento concreto cambia por conjugacion. Invertir el orden de comparacion cambia el defecto por su inverso. No se llama curvatura geometrica a Omega sin un teorema con la conexion geometrica correspondiente.

### 5.2 Defecto dirigido

Sin inversos, el dato basico es el par paralelo (P,Q), sus observadores y el tipo de comparadores. No se inventa un pseudo-inverso. Despues de una realizacion aditiva, puede definirse F(P)-F(Q); esa diferencia pertenece al destino lineal y no a la fuente por definicion.

### 5.3 Perdida y reflexion

Para un funtor F que respete los intercambios y las comparaciones de producto:

    F(P) != F(Q) => P != Q.

Si F(P)=F(Q), no se concluye P=Q sin fidelidad en ese hom-set. Un destino trenzado puede anular un defecto de la fuente. Demostrar tanto el teorema de preservacion como el de reflexion bajo hipotesis explicitas.

### 5.4 Phi/Psi independientes

Para realizaciones lineales de intercambios R_A,R_B y un mapa F:A->B:

    D_R(F)=R_B (F tensor F) - (F tensor F) R_A.

Para F:A->B y G:B->C:

    D_R(GF)=D_R(G)(F tensor F)+(G tensor G)D_R(F).

Es una identidad algebraica objetivo, sin invertir F. Demostrar versiones separadas para Phi y Psi, y para los dos recorridos. Si el transporte es monoidal no estricto, incorporar los comparadores de producto: no comparar mapas de tipos diferentes.

En un sector trenzado, Phi=c_(A,B) y Psi=c_(B,A) ejemplifican direcciones individualmente invertibles con monodromia no trivial. Eso no convierte a Psi en restriccion, dagger, adjunto o inversa de Phi. Cada identificacion tiene su propia prueba.

## 6. Modelos discriminantes obligatorios

Estos son objetivos matematicos, no pruebas Lean declaradas cerradas.

### M1: tres eventos genuinos y memoria observacional finita

Construir un EventSystem de tres eventos distintos, todos concurrentes, y sus seis historias completas. Sobre esas historias interpretar los generadores posicionales en fibras ZMod 5:

    s1(m)=-m; s2(m)=2-m.

Cada generador es involutivo; ambas rutas invierten el orden de las tres ocurrencias, pero sobre m=0 producen respectivamente 3 y 4 modulo 5. La fibra es semantica de observacion, no una nueva primitiva del EventSystem. El control del mismo tipo s1=s2=(-id) satisface la relacion ternaria. Construir la diferencia en el hom-set de la fuente mediante separacion por el interprete.

### M2: YB sin inversos

R(x,y)=(y,y) sobre Bool x Bool. Las dos rutas YB sobre Bool^3 dan (z,z,z). R no es inyectivo. Probar YB y rechazar una promocion a equivalencia. El control simetrico en el mismo portador es el flip.

### M3: trenzado no involutivo mediante Hurwitz

En un grupo G, H(a,b)=(aba^{-1},a), con inversa H^{-1}(u,v)=(v,v^{-1}uv). Probar producto conservado y relacion YB. En G=S3 obtener un par con H^2(a,b)!=(a,b). La accion de Hurwitz es sobre factorizaciones; la conexion con factorizaciones causales requiere un dominio y un funtor adicionales.

### M4: trenza pura invisible a la permutacion

Construir B2 -> S2 y distinguir id de sigma1^2 por suma de exponentes, aunque tengan igual permutacion. Los indices de hebras y la igualdad del destino no sustituyen el certificado de la fuente.

### M5: perfiles atomicos no invariantes

En B3^+, aba=bab. Los conteos de generadores son (2,1) y (1,2). La longitud total si respeta la relacion. Para una funcion aditiva a un grupo abeliano cancelativo, la relacion fuerza v(a)=v(b). Este control no invalida los sectores de factorization con multiplicidades canonicas; impide declararlos universales.

### M6: cactus autentico

Implementar la presentacion por inversiones de intervalos, construir su accion y un comparador a permutaciones. Demostrar los axiomas de un consumidor coboundary real; no basta una familia de involuciones. Registrar que la interpretacion topologica distingue el grupo cactus del puro y el cociente orbifold del espacio cociente [R1].

### M7: 3-celda no es igualdad

Construir dos rutas distintas con un comparador superior no trivial en una presentacion explicita. Rechazar una funcion que convierta toda 3-celda en igualdad salvo al pasar por el cociente que expresamente la imponga.

## 7. Aritmetica no conmutativa y restriccion

B_n^+ es el dominio de contraste para formas normales, divisibilidad lateral y fracciones; no se identifica por decreto con el monoide completo de numeros causales. Construir un dominio de procesos de intercambio y un comparador con sus endodiarios. Una correspondencia basada solo en longitud no acredita la identificacion estructural.

Reutilizar las APIs de Number/Divisibility, Residual, GCDLCM, CanonicalAtomicDomain y la localizacion Ore existente. No duplicar una segunda localizacion llamada braid fractions. Probar las hipotesis concretas que permiten consumir la construccion canónica, la inclusion y la comparacion con el grupo de trenzas [R4].

La forma normal de Garside no es un multiconjunto de atomos ni prueba unicidad de factorizacion prima. Separar palabra, elemento, forma normal, longitud y perfil invariante.

Fijar a <=_L b iff existe x, a*x=b. Si existe lcm_L(a,b)=a*(a\b) y hay cancelacion izquierda, demostrar:

    a\b <=_L x <=> b <=_L a*x.

Este complemento tiene una orientacion adjunta diferente del residuo solicitado por a*x <= b. No identificar ambos por nombre. Un complemento con esa ley no requiere que multiplicar a izquierda sea monotono en su primer argumento; declarar la variancia de cada parametro.

Distinguir efectos de dos cambios: localizar añade inversos; tomar cociente identifica rutas. Pueden combinarse, pero no son la misma operacion y no se supone que conmuten sin comparador.

## 8. Cocientes predictivos, restricciones y renormalizacion

Para una familia de observadores sobre rutas, definir indistinguibilidad local y su version contextual/predictiva: dos rutas son equivalentes cuando todo contexto y continuacion ADMITIDOS produce observaciones iguales. La version sin contextos no es automaticamente congruencia.

Construir el cociente y su propiedad universal en el dominio correspondiente. Si la familia observada crece, demostrar que el nucleo de indistinguibilidad se reduce. Construir mapas entre resoluciones y sus leyes de composicion. No asumir que añadir infinitos observadores sea computable o haga la familia conservativa.

Una restriccion de eventos o de nivel no tiene por que transportar todos los intercambios. Definir la admisibilidad del levantamiento/restriccion, demostrar cuadrados en ese dominio y conservar como obstruccion cualquier intercambio no transportable.

Obligacion local–global: las realizaciones locales y sus compatibilidades proceden de una misma fuente. Coincidencia de permutaciones locales o ausencia de defectos en cada sombra no prueba reconstruccion global; buscar un control de monodromia invisible a los observadores elegidos.

El coste de una ruta tampoco tiene por que descender a un cociente. Con pesos w1,w2, las rutas 121 y 212 cuestan 2w1+w2 y w1+2w2. Descenso exacto exige igualdad de pesos o la hipotesis pertinente; en caso contrario conservar el coste en la presentacion o formular un problema de optimizacion separado. Encontrar un representante no es demostrar que sea minimo.

## 9. Integracion con el calculo existente

El complejo cubical ordinario y su d^2=0 permanecen intactos. Una ampliacion no plana no autoriza a retirar esa ley de su dominio probado.

Construir un sistema de coeficientes/representacion sobre la categoria de intercambios y verificar los cuadrados necesarios para actuar sobre cochains. Las dos naturalezas son diferentes: intercambio combinatorio y transporte por la conexion causal. Su comparacion necesita una prueba.

Si el transporte induce mapas de complejos, obtener la accion en cohomologia con los productores existentes. Para Hodge, exigir por separado las compatibilidades con d, delta y Delta. Para espectro, usar un entrelazador real de operadores, no igualdad de listas de autovalores. Si no hay plano, conservar un defecto de transporte; no afirmar cohomologia ordinaria de un operador cuyo cuadrado no se anula.

Si se propone un calculo exterior trenzado, comenzar como realizacion especializada. Probar el producto, el cociente de alternancia adecuado, el diferencial y su Leibniz; no sustituir el wedge clasico por una relacion ad hoc. La caracteristica del cuerpo, orden del parametro y dimensiones son hipotesis locales.

## 10. Clausura, dualidad y nivel superior

Separar inverse exchange, reflection/dagger, dual algebraico, adjunto Hilbert y restriccion correlativa. Probar las compatibilidades de cierre de diarios antes de afirmar un invariante de cierres.

Una estructura ribbon exige trenzado, dualidad/rigidez y twist compatibles; no se obtiene de un grupo B_n aislado. La invariancia de una traza por conjugacion no garantiza invariancia por estabilizacion de Markov. Añadir esas leyes solo en la familia de representaciones y rango donde se prueben.

En la capa superior, declarar dimension exacta: categorias de caminos, presentaciones de 2-celdas, 3-celdas y coherencias verificadas. No llamar infinity-categoria a una estructura truncada. Los pentagonos y hexagonos presentes como 3-celdas necesitan sus relaciones superiores cuando se reclame ese nivel. Reutilizar categorias nativas de mathlib y productores existentes antes de definir infraestructura nueva [R5].

El horizonte de trenzas parentizadas, compleciones profinitas y Grothendieck–Teichmuller es una realizacion avanzada. Su fuente debe tener operaciones, asociadores y compatibilidad de torre efectivamente construidos; una familia de B_n independientes no basta. Horel [R8] es una referencia externa para el destino, no una prueba de reconstruccion aritmetica de nuestros numeros causales.

## 11. Orden de implementacion sin bloqueo cruzado

CX00: inventario y firmas, alcance de cada productor, ausencia de regresiones.
CX01/CX02: eventos concretos, pasos tipados, categoria libre, contextos y cocientes universales.
CX03/CX04: paquetes de leyes y discriminadores; primeras realizaciones ECIA en paralelo.
CX05: defectos, invariancia de presentacion y transportes independientes Phi/Psi.
CX06: trenzas positivas/Garside/Ore y auditoria de perfiles.
CX07: perdida contextual, renormalizacion y restricciones.
CX08: conexiones con cochains/Hodge bajo las hipotesis exactas.
CX09: cierres y datos ribbon de fuente.
CX10: consumidores ECIA progresivos, sin esperar al cierre total de CX06–09.
CX11: auditoria transversal aplicada desde cada incremento, no al final solamente.

Una fila que solo declara una estructura cuyo campo es el teorema buscado queda INTERFACE, no THEOREM. Cada paquete de leyes debe tener un constructor/modelo y un resultado de suficiencia/independencia. Los primeros controles no sustituyen las obligaciones generales de los sectores.

## 12. Referencias externas y estatuto

Las referencias justifican estructuras matematicas conocidas. Las conexiones concretas con nuestros diarios, su aritmetica y ECIA son objetivos de CX, no resultados atribuidos a esos autores.

[R1] Henriques–Kamnitzer, Crystals and coboundary categories, arXiv:math/0406478v3, https://arxiv.org/html/math/0406478v3 .
[R2] Naik–Nanda–Singh, Some remarks on twin groups, arXiv:1912.01466, https://arxiv.org/abs/1912.01466 .
[R3] McCurdy–Street, What Separable Frobenius Monoidal Functors Preserve, arXiv:0904.3449v4, https://arxiv.org/html/0904.3449v4 .
[R4] Dehornoy, Garside and quadratic normalisation: a survey, arXiv:1504.07788v1, https://arxiv.org/html/1504.07788v1 .
[R5] Guiraud–Malbos, Identities among relations for higher-dimensional rewriting systems, arXiv:0910.4538v2, https://arxiv.org/abs/0910.4538 .
[R6] Theorem Proving in Lean 4, Propositions and Proofs, https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/ .
[R7] Mathlib CategoryTheory.PathCategory.Basic y Monoidal.Braided.Basic, documentacion upstream consultada 2026-09-28; cotejar nombres con v4.32.1 antes de implementar: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/PathCategory/Basic.html y https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monoidal/Braided/Basic.html .
[R8] Horel, Profinite completion of operads and the Grothendieck–Teichmuller group, arXiv:1504.01605, https://arxiv.org/abs/1504.01605 .
