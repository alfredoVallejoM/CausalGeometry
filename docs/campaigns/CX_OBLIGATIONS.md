# CX — Registro operativo de obligaciones

Fecha: 2026-09-28. Estado de TODAS las filas: PLANNED / NOT ACCREDITED.
Documento padre: CX_EXCHANGE_COHERENCE.md.

## 0. Contabilidad y evidencias

Hay 12 bloques CX00–CX11 con 8 filas cada uno: 96 subobligaciones de esta ampliacion. No se suman automaticamente a las 636 filas historicas ni se incorporan por nombre al enumerado Lean. Son descomposicion transversal y extension documentada del alcance; no se borran ni reacreditan filas anteriores.

Cada fila requiere: enunciado con universos/dominio/hipotesis; productor de datos; prueba y consumidor; control positivo; mutacion relevante; auditoria de imports y axiomas; coste cuando sea material; evidencia local por SHA. Cuando una independencia no tenga sentido, marcar la mutacion como no aplicable con justificacion, no inventar un contraejemplo. Un rechazo por error de tipos solo acredita la frontera de interfaz, no una imposibilidad matematica general.

SOURCE-VERIFIED no exige ECIA: el consumidor puede ser un teorema o modelo del propio nucleo. REALIZATION-VERIFIED exige ademas el consumidor real del destino y ambos SHAs. INTERFACE, SOURCE-WRITTEN, LEAN-TYPECHECKED y CAMPAIGN-ACCREDITED son estados distintos.

Dependencias entre bloques indican el orden matematico, no una obligacion de terminar un bloque entero antes de una fila que usa solo una parte. CX11 se ejecuta por incremento desde CX00; sus auditorias no forman ciclos de importacion con los productores.

## CX00 — Gobierno, reutilizacion y alcance

Propietario: fuente. Padres: CA00, CA10, CA15. No depende de ECIA.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX00.01 | Fijar una matriz de fronteras/objetos/historias/intercambios/celdas y equivalencias. | Igual extremo no se registra como igual ruta. |
| CX00.02 | Inventariar productores reales EventSystem, Path, Diary, PairedTransform, realizaciones, cochains y Ore. | Cada reutilizacion tiene modulo y declaracion comprobados, no solo nombre de fichero. |
| CX00.03 | Auditar APIs de mathlib en el pin exacto para caminos, quivers, categorias, grupos presentados y trenzado. | La disponibilidad upstream no se confunde con disponibilidad en el pin. |
| CX00.04 | Establecer datos relevantes en Type y predicados de validez en Prop. | Un modelo con dos intercambios del mismo hom-set sigue distinguiendolos. |
| CX00.05 | Publicar el cruce CX con las filas historicas sin renumerar ni eliminar obligaciones. | Se conserva la cardinalidad y el contenido del ledger formal anterior. |
| CX00.06 | Separar cierre autonomo, cierre de realizaciones y horizontes analiticos. | Un destino pendiente no invalida un productor fuente ya acreditado. |
| CX00.07 | Registrar contratos de coste con todos los parametros no constantes. | Rango, longitud, anchura, dimension y tamaño de certificado no desaparecen. |
| CX00.08 | Congelar alcance excluido: sin cambios a ontologia primaria, acciones CI o motivo dinamico. | Diff de cada incremento prueba ausencia de modificaciones no autorizadas. |

Salida: inventario verificado y diseno tipado; no requiere implementar grupos de trenzas.

## CX01 — Historias y pasos de intercambio

Propietario: fuente. Padres: CA01/02/03, CA13.15. Depende de CX00.01–04.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX01.01 | Definir la familia de historias con fronteras a partir de los productores causales existentes. | No se crea una segunda nocion de evento o historia sin comparador. |
| CX01.02 | Construir un sistema causal de tres eventos distintos concurrentes y sus historias. | Mismo label no autoriza reutilizar una ocurrencia consumida. |
| CX01.03 | Construir ExchangeStep h k con localizacion del intercambio y prueba de admisibilidad. | Evento dependiente/conflictivo no admite el intercambio por defecto. |
| CX01.04 | Derivar preservacion de extremos de cada paso cronologico del diamante real. | No se almacena solo la conclusion sin consumir el diamante. |
| CX01.05 | Construir insercion de un paso en contextos izquierdo y derecho admitidos. | Se rechaza un contexto que destruye habilitacion. |
| CX01.06 | Conservar tipos/colores/identidad de componentes en intercambios paralelos. | Una transposicion de posiciones no sustituye un isomorfismo entre tipos. |
| CX01.07 | Separar sintaxis de intercambio cronologico, paralelo y de factorizacion. | No existe coercion automatica entre las tres interpretaciones. |
| CX01.08 | Definir intercambio opcional de fronteras diferentes mediante un comparador explicito. | La igualdad de fronteras no se obtiene por borrar sus indices. |

Salida: pasos genuinos sobre el dominio causal, no un grafo de etiquetas desligado de eventos.

## CX02 — Composicion, contextos y cocientes

Propietario: fuente. Padres: CA02/03, CA10. Depende de CX01.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX02.01 | Construir la categoria libre de caminos del quiver de pasos y sus leyes. | Dos palabras de pasos distintas no colapsan por tener iguales extremos. |
| CX02.02 | Extender una interpretacion de generadores a un funtor y demostrar su unicidad. | Universalidad es un teorema de construccion, no solo un campo. |
| CX02.03 | Extender los contextos a caminos y demostrar identidad/composicion. | Whiskering conserva indices y certificados de habilitacion. |
| CX02.04 | Construir congruencia generada por relaciones paralelas y estable por contextos. | Una relacion sobre extremos solos no se acepta como congruencia de rutas. |
| CX02.05 | Construir el cociente y probar el criterio de factorizacion del interprete. | Respeto de relaciones generadoras se propaga por prueba a toda la congruencia. |
| CX02.06 | Construir comparadores de cocientes para inclusion de politicas de relaciones. | Direccion de perdida correcta: mas relaciones permiten mas colapsos. |
| CX02.07 | Construir inversion solo del subsistema seleccionado, con propiedad universal. | No se interpreta la inversion formal como deshacer eventos causales. |
| CX02.08 | Demostrar las leyes horizontales/verticales exigidas por la estructura categorica reclamada. | No se llama bicategoria a una interfaz sin intercambio/coherencias demostrados. |

Salida: infraestructura libre y cocientes con semantica, independiente de que YB sea verdadera.

## CX03 — Leyes independientes y recuperacion de sectores

Propietario: fuente. Padres: CA03, CA13.15, CA17. Depende de CX02 en los dominios usados.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX03.01 | Definir reversibilidad con inversos especificados de pasos/rutas. | Inverso de intercambio no se identifica con dagger o restriccion. |
| CX03.02 | Definir conmutatividad lejana con el soporte y la independencia requeridos. | Ausencia de solapamiento sintactico no sustituye independencia semantica. |
| CX03.03 | Definir las dos rutas ternarias P,Q con todos sus tipos y contextos. | Se rechaza una comparacion entre composiciones de tipos diferentes. |
| CX03.04 | Construir una accion de B_n^+ desde generadores que satisfagan las relaciones. | La accion se deriva de la presentacion, no se añade como etiqueta. |
| CX03.05 | Extender la accion a B_n exactamente bajo invertibilidad demostrada. | El operador no inyectivo de CX04.03 no pasa este criterio. |
| CX03.06 | Construir el cociente simetrico y el comparador con la concurrencia historica. | Involutividad sola no se usa para deducir simetria. |
| CX03.07 | Construir paquetes monoidales trenzado y coboundary con sus leyes propias. | YB en un objeto no se promueve a naturalidad/hexagonos de toda la categoria. |
| CX03.08 | Declarar y probar cada flecha de olvido/recuperacion entre sectores soportados. | No se publica una cadena falsa que ordene todos los sectores por inclusion. |

Salida: sectores caracterizados por construcciones y teoremas, no por booleanos sin significado.

## CX04 — Modelos y contraejemplos del mismo tipo

Propietario: fuente. Padres: CA00/13/15/17. Depende de CX01–03 segun el modelo.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX04.01 | Realizar los intercambios de tres historias sobre fibras ZMod 5 mediante -m y 2-m. | Rutas 121 y 212 envian 0 a 3 y 4; mismo orden final. |
| CX04.02 | Construir el control del mismo tipo con ambas reflexiones -id. | La relacion ternaria se verifica y los datos causales de base no cambian. |
| CX04.03 | Probar YB para R(x,y)=(y,y) en Bool^2 y refutar inyectividad. | Se distinguen coherencia de trenza e invertibilidad. |
| CX04.04 | Probar inversa, YB y conservacion de producto para Hurwitz en grupos. | Un ejemplo en S3 refuta involutividad del mismo operador. |
| CX04.05 | Construir id y sigma1^2 con igual permutacion y distinta suma de exponentes. | Pérdida de informacion pura no se infiere solo de una figura. |
| CX04.06 | Construir aba=bab en B3^+ y el fallo de conteo atomico por generador. | La longitud total sobrevive; no se elimina el control positivo. |
| CX04.07 | Construir un modelo cactus/coboundary autentico con sus relaciones de intervalos. | Una familia arbitraria de involuciones no satisface automaticamente el contrato. |
| CX04.08 | Construir rutas distintas con 3-celda explicita y conservar esa distincion. | El modelo no identifica existencia de 3-celda con igualdad Lean. |

Salida: controles no vacuos, conectados a las fuentes cuando se reclame causalidad; las identidades generales no se sustituyen por enumeracion finita.

## CX05 — Defectos, cambios de presentacion y Phi/Psi

Propietario: fuente. Padres: CA09/10/17/21. Depende de CX02/03.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX05.01 | Definir Omega=Q^{-1}P donde hay inversos y demostrar Omega=id iff P=Q. | No se acepta la definicion fuera del dominio reversible. |
| CX05.02 | Probar la ley de conjugacion de Omega bajo cambio de frontera/presentacion. | Se distingue igualdad del elemento de invariancia de su clase/conclusion. |
| CX05.03 | Construir el defecto dirigido como par paralelo con observadores y comparadores. | Ningun pseudo-inverso aparece en la fuente general. |
| CX05.04 | Probar que separar imagenes separa fuentes y que igualdad de imagenes requiere fidelidad para reflejarse. | Un destino trenzado que colapsa rutas no hace trenzada toda fuente. |
| CX05.05 | Definir D_R(F) en el sector lineal con comparadores de producto correctos. | Phi y Psi tienen defectos independientes. |
| CX05.06 | Probar D_R(GF)=D_R(G)(F tensor F)+(G tensor G)D_R(F). | No se introduce invertibilidad para una identidad que no la necesita. |
| CX05.07 | Derivar los defectos de ambos recorridos Phi/Psi por la ley de composicion. | Un control conserva una direccion y falla en la contraria. |
| CX05.08 | Construir una realizacion de monodromia del par sin identificar Psi con inversa/adjunta. | Ambos mapas pueden ser invertibles y su compuesto no ser identidad. |

Salida: defectos observables y transportables con hipotesis minimas.

## CX06 — Aritmetica positiva, Garside y localizacion

Propietario: fuente. Padres: CA06/07/18/22. Depende de CX03.04/05 y modelos pertinentes.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX06.01 | Construir el dominio positivo de procesos de intercambio y su comparador con B_n^+. | Igual longitud no basta para demostrar equivalencia de estructuras. |
| CX06.02 | Instanciar divisibilidad izquierda/derecha y cancelacion en el dominio soportado. | No se fuerza conmutatividad ni se confunden orientaciones. |
| CX06.03 | Construir gcd/lcm laterales y demostrar sus propiedades universales. | Un algoritmo que devuelve un candidato no acredita minimalidad/maximalidad. |
| CX06.04 | Construir complemento de lcm y demostrar su ley adjunta exacta. | No se sustituye la desigualdad b<=a*x por a*x<=b. |
| CX06.05 | Construir forma normal, correccion, unicidad y decision en el sector de Garside declarado. | Normalidad canonica no se confunde con multiplicidades primas unicas. |
| CX06.06 | Probar que longitud desciende y que una valuacion aditiva a grupo abeliano identifica los atomos adyacentes. | No se publica un perfil por generador que viole aba=bab. |
| CX06.07 | Instanciar las hipotesis de Ore y comparar la localizacion canonica con el grupo de trenzas. | No se reimplementa otro cociente fraccionario ni se supone reversibilidad ausente. |
| CX06.08 | Publicar complejidad de la normalizacion concreta incluyendo rango, operaciones locales y certificados. | No se oculta una tabla de n! elementos simples. |

Salida: dominio no conmutativo exigente para la aritmetica causal; las APIs mas generales permanecen generales.

## CX07 — Perdida contextual, restricciones y renormalizacion

Propietario: fuente. Padres: CA09.13–24, CA10/14/17/19. Depende de CX02/05.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX07.01 | Definir equivalencia observacional sobre rutas paralelas con fuente comun. | No se comparan datos ensamblados de fuentes distintas. |
| CX07.02 | Construir la version estable bajo todos los contextos/continuaciones admitidos. | Igualdad de observacion sin contexto no se promueve a congruencia. |
| CX07.03 | Construir cociente predictivo y su propiedad universal. | No se afirma que sea computable o finito sin hipotesis. |
| CX07.04 | Probar refinamiento por ampliacion de observadores y composicion de comparadores. | Mas observadores implican menos indistinguibilidad, no al reves. |
| CX07.05 | Construir restricciones de intercambios sobre dominios de levantamiento declarados. | Una restriccion de eventos no transporta todo intercambio automaticamente. |
| CX07.06 | Caracterizar perdida de monodromia pura y obstruccion a reconstruir rutas. | El mismo resultado en S_n no acredita recuperacion de B_n. |
| CX07.07 | Construir un control local–global con compatibilidad de fuente y posible perdida conjunta. | Coincidencia de todas las sombras elegidas no implica conservatividad sin prueba. |
| CX07.08 | Probar criterio de descenso de costes o conservar el coste en la presentacion. | 121 y 212 con pesos desiguales refutan coste invariante automatico. |

Salida: renormalizacion de procesos que declara que informacion operacional conserva.

## CX08 — Cochains, conexiones y Hodge

Propietario: fuente. Padres: CA09, CA21. Depende de CX05 y productores graduados existentes.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX08.01 | Construir representacion de intercambios en coeficientes sin cambiar EventSystem. | La memoria observacional no se introduce como evento primitivo. |
| CX08.02 | Probar condiciones exactas para inducir mapas del complejo cubical existente. | Un mapa arbitrario de coeficientes no es automaticamente mapa de complejos. |
| CX08.03 | Conectar defectos de intercambio con defectos diferenciales por un cuadrado probado. | Omega no se identifica por nombre con curvatura de la conexion. |
| CX08.04 | Inducir accion en cohomologia cuando se anula el defecto de d. | No se reclama cohomologia ordinaria si el diferencial elegido no es square-zero. |
| CX08.05 | Probar transporte armonico bajo compatibilidad de Delta y las hipotesis existentes. | Compatibilidad de d sola no implica la de delta. |
| CX08.06 | Consumir entrelazadores espectrales en sectores finitos demostrados. | Igualdad de autovalores listados no reemplaza el entrelazador. |
| CX08.07 | Formular y realizar un calculo exterior trenzado separado, con producto y Leibniz certificados. | No se altera el wedge clasico para acomodar una relacion nueva. |
| CX08.08 | Probar recuperacion del calculo historico bajo especializacion simetrica compatible. | Las firmas y resultados anteriores quedan como regresion obligatoria. |

Salida: conexiones matematicas con el calculo existente, no una segunda teoria paralela de Hodge.

## CX09 — Cierres, dualidad y coherencias superiores

Propietario: fuente. Padres: CA03/08/11/13.15–17. Depende de CX02/03 y gluing existente.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX09.01 | Probar compatibilidad de cierre de diarios con transformaciones admitidas. | No se equiparan cierre de palabra, traza y enlace por definicion. |
| CX09.02 | Construir reflexion/dagger y comparar con inversion solo donde se demuestre. | Un control separa orientacion inversa de restriccion correlativa. |
| CX09.03 | Construir duales y sus identidades triangulares en el dominio soportado. | Dar un objeto llamado dual no acredita rigidez. |
| CX09.04 | Construir twist y su compatibilidad ribbon con trenzado y duales. | Trenzado sin esos datos no se promueve a ribbon. |
| CX09.05 | Demostrar invariancia ciclica/conjugacion de las trazas elegidas. | No se confunde con invariancia bajo cambio de rango. |
| CX09.06 | Enunciar y demostrar estabilizacion de Markov en una familia concreta. | Exito a rango fijo no acredita todos los rangos. |
| CX09.07 | Construir 3-celdas y las coherencias de la dimension reclamada. | Una presentacion truncada no se declara infinity-categoria. |
| CX09.08 | Construir la comparacion parentizada/estricta con la informacion que preserva. | Se registran por separado coherencia asociativa y perdida de intercambios. |

Salida: sectores de cierre y enriquecimiento superior explicitamente delimitados.

## CX10 — Realizaciones ECIA/GenContinuum en paralelo

Propietario: realizacion downstream. Padres: CA11/13/14/19/23/24/25. Cada fila depende SOLO de sus productores fuente.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX10.01 | Construir un interprete real de pasos y rutas en un destino nativo ECIA con procedencia. | No basta elegir objetos de igual dimension o agregar campos nominales. |
| CX10.02 | Construir realizacion lineal no simetrica y su defecto detectado/preservado. | La igualdad del observador numerico no borra el defecto estructural. |
| CX10.03 | Conectar Phi/Psi de restricciones/filtraciones con intercambios mediante cuadrados propios. | La adjuncion de filtraciones no implica naturalidad del trenzado. |
| CX10.04 | Realizar transformaciones de factorizaciones causales mediante Hurwitz en un dominio aritmetico nombrado. | Producto igual no hace iguales las factorizaciones. |
| CX10.05 | Instanciar braid/dual/twist/cierre en un consumidor ribbon real. | Se reutiliza el destino existente; si falta, se construye y no se declara disponible. |
| CX10.06 | Publicar perdida y fidelidad de objetos, historias, rutas y celdas por separado. | Fidelidad sobre objetos no se traslada automaticamente a hom-categorias. |
| CX10.07 | Construir una familia comun de realizaciones con comparadores de cohomologia/trazas locales. | Mezclar fuentes o unificar por un solo indice invalida el contrato. |
| CX10.08 | Especificar y desarrollar los teoremas de comparacion avanzada: torres parentizadas/profinitas y destinos aritmeticos. | No hay promocion a Galois/GT, Hecke aritmetico o Fredholm por analogia. |

Salida: cada consumidor tiene gate propio; no obliga a cerrar todo el horizonte para acreditar uno finito.

## CX11 — Auditoria y validacion por incremento

Propietario: transversal, sin dependencia circular de imports. Padres: CA00/15, CA22.40, CA23.31.

| ID | Resultado obligatorio | Criterio discriminante |
|---|---|---|
| CX11.01 | Validar la matriz literal de filas, dependencias, modelos y enunciados. | Ninguna fila desaparece o se cierra por un cambio de nombre. |
| CX11.02 | Ejecutar controles positivos y mutaciones del mismo tipo sobre el alcance modificado. | No se usa solo un test que falla por no compilar. |
| CX11.03 | Publicar coste de datos, operaciones y certificados con presupuestos reproducibles. | Timeout se registra como tal; no es prueba de no equivalencia. |
| CX11.04 | Ejecutar Lean real y registrar #print axioms/imports/higiene por SHA. | Auditoria textual o simulador finito no se anuncia como kernel PASS. |
| CX11.05 | Verificar consumidores historicos afectados por el cono de dependencias. | No se elimina el sector simetrico o aritmetico previo para pasar tests. |
| CX11.06 | Auditar independencia del nucleo y ausencia de workflows/pins cambiados sin mandato. | Ningun import ECIA entra en CausalGeometry. |
| CX11.07 | Acreditar cada adaptador con source SHA, downstream SHA, pin resuelto y pruebas de destino. | Este gate no se exige a filas puramente fuente. |
| CX11.08 | Publicar recibo de alcance, fallos conservados, limitaciones y revision adversaria real. | No se atribuye independencia a una autorrevision ni se sobrescriben fallos. |

## Cruce con el programa acumulado

| Programa padre | Aporte CX | Lo que sigue independiente |
|---|---|---|
| CA02/03 | Historias transformables, gluing de intercambios y coherencias | Terminacion de productores historicos faltantes |
| CA06/07/18/22 | Dominio positivo no conmutativo, perfiles, complementos y Ore | Toda aritmetica fuera del dominio demostrado |
| CA09 | Cocientes semanticos/predictivos, restricciones y defectos | Ejes d_v/d_h/d_mu y renormalizacion general |
| CA10/14/19 | Perdida en rutas y celdas, fuente comun y reconstruccion | Conservatividad global no demostrada |
| CA11/13.15–17 | Extension general, sector trenzado y realizacion ribbon | Rutas MW/Selmer, operadoriales y espectrales previas |
| CA17 | Phi/Psi y adjunciones con orientacion explicita | Restriccion no se identifica con inverso o dagger |
| CA21 | Mapas de complejos, Hodge y especializaciones | No se reescribe el complejo cubical existente |
| CA23/24 | Consumidores reales y monodromia aritmetica | Tate, Tamagawa, Frobenius, Hecke y demas rutas conservadas |
| CA25 | Hipotesis analiticas al pasar a completaciones/operadores infinitos | Ninguna inferencia RH/BSD/Langlands automatica |

## Gates y concurrencia del trabajo

G-CX-FOUNDATION: CX00, CX01, CX02, CX03 y los discriminadores usados; mas CX11.01–06/08 en ese alcance.
G-CX-DEFECT: CX05 y sus modelos, sin depender de ECIA.
G-CX-ARITHMETIC: CX06, hipotesis Ore y controles de perfiles; sin depender del consumidor ribbon.
G-CX-QUOTIENT: CX07 y la teoria abstracta de realizaciones.
G-CX-CALCULUS: CX08 y productores CA21 exactos.
G-CX-CLOSURE: CX09 en el dominio/rango declarado.
G-CX-ECIA-<consumer>: la fila CX10 correspondiente, sus productores precisos y CX11.07/08.

No existe un unico PASS que pueda esconder un sector pendiente. El cierre de CX completo exige reconciliar todos sus sectores y registrar explicitamente los horizontes aun no probados; la acreditacion de un productor local no espera ese cierre global.
