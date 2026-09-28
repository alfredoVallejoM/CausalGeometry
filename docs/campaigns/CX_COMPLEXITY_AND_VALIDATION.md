# CX — Complejidad, controles adversarios y validacion

Fecha: 2026-09-28. Estado: CONTRATOS DE PLANIFICACION; sin nuevos benchmarks ni acreditacion Lean.
Relacion: CX_EXCHANGE_COHERENCE.md y CX_OBLIGATIONS.md.

## 1. Principio de coste

Generalidad algebraica, decidibilidad y eficiencia son propiedades distintas. Un cociente puede existir sin un normalizador efectivo; una representacion finita puede distinguir una pareja sin decidir toda igualdad de la fuente; un algoritmo correcto puede producir certificados mayores que su salida normalizada.

Toda operacion debe declarar: representacion, dominio, tamaño de entrada, coste aritmetico/bit, tiempo, memoria maxima, tamaño de salida/certificado, estrategia de cache, modo incremental y limites. Las cotas siguientes son contratos derivados de algoritmos descritos o metas condicionadas, no mediciones de una implementacion que aun no existe.

## 2. Parametros que no pueden ocultarse

| Simbolo | Significado |
|---|---|
| e | Numero de ocurrencias de evento almacenadas |
| m_c, m_f | Aristas causales y conflictos representados |
| h | Longitud de una historia de eventos |
| w | Anchura habilitada/concurrente del estado considerado |
| n | Numero de componentes/hebras del sector |
| ell | Longitud de una palabra de intercambios |
| r, p | Numero de esquemas de relacion y longitud maxima de patron |
| s | Numero de pasos de un certificado de reescritura |
| L_max | Longitud maxima de un intermedio en ese certificado |
| V, E | Vertices/aristas efectivamente materializados en una exploracion |
| k | Cota de profundidad de busqueda, no garantia de completitud |
| d | Dimension local de una fibra lineal |
| N=d^n | Dimension de un estado tensorial completo |
| z | Numero de coeficientes no nulos efectivamente almacenados |
| b | Longitud de bits maxima de coeficientes/identificadores aritmeticos |
| C_adm | Coste de comprobar un paso causal admitido |
| C_eq | Coste de igualdad exacta de labels/coeficientes usados |
| C_loc(n,b) | Coste de la operacion local del normalizador certificado |
| S_proof | Tamaño serializado o nodos compartidos del certificado Lean |

Los parametros e,h,n no se identifican: un numero de hebras fijo puede soportar palabras largas; un diario puede contener creacion/fusion y no tener rango fijo.

## 3. Construccion de pasos y observadores

### 3.1 Habilitacion

Para grafos explicitos, auditar lectura y validacion de causalidad/conflicto con m_c,m_f. Una representacion densa puede costar O(e^2) memoria. Un indice de predecesores no es gratis: incluir construccion, actualizacion e invalidacion.

Enumerar todos los pares de eventos de una frontera de anchura w cuesta O(w^2*C_adm) con prueba independiente por pareja. Enumerar todos los triples candidatos cuesta O(w^3*C_adm) bajo el mismo modelo. No usar esos costes para afirmar que enumerar todas las historias es polinomico.

Con h eventos distintos todos independientes existen h! ordenaciones completas. El modelo debe operar sobre generadores y consultas locales, no materializar por defecto todas las linealizaciones. Dos historias seleccionadas y el teorema generico de contexto son preferibles a una tabla factorial.

### 3.2 Palabras y caminos

Almacenar una palabra explicita cuesta O(ell). Verificar sus indices y ejecutar cada generador cuesta O(ell*C_adm) mas el coste de actualizar la representacion de la historia. Si cada paso copia una lista de longitud h, el coste real es O(ell*h), no O(ell).

Un arbol persistente puede reducir copias y compartir subrutas; la cota exige declarar altura, balanceo, identificadores de contexto e invalidacion. Un nodo de concatenacion es O(1) solo para construir la referencia; aplanar/imprimir toda la palabra sigue costando al menos su longitud.

Calcular la sombra de permutacion mediante un array de n posiciones y ell intercambios validos cuesta O(n+ell) operaciones de palabra y O(n) memoria. La suma de exponentes usa O(ell) adiciones con enteros de tamaño O(log(ell+1)); no es un algoritmo para decidir equivalencia general de trenzas.

Hashing puede ayudar a indexar sintaxis, pero un hash coincidente no prueba igualdad ni fidelidad. Un hash distinto solo separa aquello cuya invariancia ya se haya probado; el hash de palabra cruda no es invariante de cociente.

## 4. Busqueda, reescritura y certificados

### 4.1 Explorar no es decidir

En un grafo EXPLICITO finito, BFS cuesta O(V+E), mas igualdad/indexacion y generacion de nodos. Cuando el grafo es implicito, V y E incluyen todos los estados generados. Un limite k no convierte una respuesta negativa en prueba de no equivalencia.

Resultados previstos:

* EQUAL con certificado verificable.
* DISTINCT con invariante separador probado o un normalizador completo del dominio.
* INCONCLUSIVE con presupuesto, motivo y frontera de exploracion.

Exhaustar tiempo, memoria o profundidad devuelve INCONCLUSIVE. La ausencia de un testigo encontrado no se registra como DISTINCT.

La cantidad de palabras de longitud ell sobre los n-1 generadores positivos es (n-1)^ell antes de imponer relaciones; con inversos puede crecer como [2(n-1)]^ell. Estas cifras describen el espacio ingenuo de palabras, no el numero de elementos distintos. Su uso es prohibir enumeraciones ocultas.

### 4.2 Verificacion de una prueba frente a su busqueda

Para un certificado explicito de s reescrituras con intermedios de longitud <=L_max, un verificador ingenuo que compara y copia contextos cuesta O(s*L_max*C_eq) mas las comprobaciones de admisibilidad. Si solo conserva actual/siguiente, su memoria de trabajo puede ser O(L_max), pero el certificado completo cuesta O(s*L_max) si almacena cada intermedio.

Con referencias a subpalabras y esquemas locales, separar memoria del verificador, tamaño comprimido del certificado y tamaño de expansion. No declarar memoria lineal total cuando la evidencia serializada es cuadratica o mayor.

Para reglas de cadenas finitas, un enumerador ingenuo de solapamientos puede recorrer O(r^2*p^2) candidatos, mas matching. Esa cota no se traslada a poligrafos arbitrarios ni a coherencias superiores sin un algoritmo especifico.

### 4.3 Normalizacion certificada

No orientar aba=bab arbitrariamente y deducir terminacion/confluencia. La prueba de forma normal requiere estrategia, medida o resultado de normalizacion, estabilidad contextual y unicidad en el cociente.

Para un normalizador de tipo Garside con calendario probado de O(ell^2) operaciones locales, el contrato util es O(ell^2*C_loc(n,b)), mas lectura, conversion y certificado. La hipotesis sobre el calendario debe consumirse de un teorema correspondiente al normalizador usado. La palabra quadratic en quadratic normalisation describe localidad de reglas de longitud dos, no por si sola una cota cuadratica de todas las estrategias [R4 del documento principal].

No confundir coste de una estrategia de normalizacion elegida con longitud de CUALQUIER secuencia de reescritura. El estudio de Dehornoy distingue ambos resultados.

En trenzas de rango n, hay n! elementos simples en la estructura clasica de Garside. Representarlos mediante permutaciones no implica almacenarlos todos. Una implementacion que precalcula su tabla debe registrar explicitamente esa memoria y solo puede reclamar eficiencia para el rango acotado del experimento.

Decision de igualdad, conjugacion, equivalencia de cierres y busqueda de representante de coste minimo son problemas diferentes. Un normalizador de palabras no acredita los otros tres.

## 5. Operadores Yang–Baxter y tensores

Para una fibra de dimension d, un operador R sobre V tensor V tiene d^4 entradas densas. Sobre tres factores, R12 y R23 actuan en dimension d^3.

Una comprobacion mediante matrices densas explicitas de dimension d^3 puede costar O(d^9) operaciones escalares y O(d^6) memoria. Es una cota del algoritmo ingenuo de multiplicacion cubica, no una barrera inferior ni una recomendacion.

Aplicar un operador d^2 x d^2 a dos posiciones de un estado tensorial d^n por contracciones locales cuesta O(d^(n+2)) operaciones escalares por cruce y O(d^n+d^4) memoria bajo almacenamiento denso. Para ell cruces: O(ell*d^(n+2)), con crecimiento de bits de coeficientes registrado aparte. Materializar el operador global necesita O(d^(2n)) coeficientes; no se debe hacer para una consulta que solo necesita su accion sobre un estado.

La escasez se mide por z y por el coste real de generar/combinar entradas. Un operador inicialmente disperso puede densificarse por composicion. No fijar z constante ni prometer que toda renormalizacion evita la explosion tensorial.

En aritmetica exacta, contar operaciones de campo y operaciones de bits por separado. Para racionales, registrar crecimiento de numeradores/denominadores y normalizacion. Para campos finitos, registrar modulo, grado y representacion. Numerica aproximada no demuestra una igualdad de operadores Lean; requiere una afirmacion distinta con error certificado.

## 6. Corpus matematico minimo y mutaciones

Cada caso debe conservar su positivo y la mutacion dentro de la MISMA firma siempre que se este afirmando independencia matematica.

| Control | Positivo | Mutacion o frontera | Resultado que se exige |
|---|---|---|---|
| EVENTS-3 | Tres eventos distintos concurrentes | Introducir dependencia/conflicto o repetir ocurrencia | Solo intercambios admitidos |
| TWIN-3 | Reflexiones -m y 2-m sobre ZMod 5 | Afirmar YB porque son involutivas | Rutas sobre 0 dan 3 != 4 |
| SYMMETRIC-3 | Ambas reflexiones -m | Afirmar que siempre existe defecto | Rutas ternarias coinciden |
| YB-NONINV | R(x,y)=(y,y) en Bool^2 | Promover R a equivalencia | YB verdadera e inyectividad falsa |
| YB-HURWITZ | H(a,b)=(aba^-1,a) | Sustituir por swap de factores sin conjugacion en grupo no abeliano | Producto/YB probados para H; perdida bajo mutacion |
| BRAID-NONSYM | H sobre pares de S3 | Inferir H^2=id desde invertibilidad | Par concreto refuta involutividad |
| PURE-LOSS | id y sigma1^2 en B2 | Reconstruir desde S2 | Permutacion igual y exponente distinto |
| PROFILE | aba=bab en B3^+ | Perfil por conteo independiente de atomos | Longitud desciende, perfil no |
| RESIDUAL | Complemento lcm con ley correcta | Invertir orientacion de desigualdad | Ley solo con su variancia probada |
| COHERENCE-3 | Rutas distintas y comparador superior | Convertir toda 3-celda en igualdad | La conversion exige cociente adicional |
| PHI-PSI | Una direccion respeta R | Deducir compatibilidad de la otra | Defectos independientes |
| COST | Pesos iguales en generadores | Pesos distintos y coste declarado invariante | 121/212 discriminan |
| FINITE-SEARCH | Prueba/invariante certificado | Timeout declarado desigualdad | Resultado INCONCLUSIVE |
| FIDELITY | Interpretacion fiel en hom-set | Igualdad de sombras declarada fidelidad | Reflexion solo bajo hipotesis |
| CACTUS | Relaciones de intervalos verificadas | Solo involuciones sin coherencia | No hay promocion a coboundary |
| MARKOV | Familia con estabilizacion probada | Solo traza ciclica a rango fijo | No hay invariante general de cierre |

No atribuir a una mutacion mas de lo que demuestra. El modelo de ZMod 5 separa una pareja de rutas y permite un test finito; no es una representacion fiel de todo T3. La representacion de Hurwitz sobre S3 verifica un modelo, no reconstruye todas las trenzas.

## 7. Arquitectura Lean prevista

Rutas candidatas, aun no creadas por esta entrega:

    CausalGeometry/Exchange/Basic.lean
    CausalGeometry/Exchange/Context.lean
    CausalGeometry/Exchange/Path.lean
    CausalGeometry/Exchange/Relation.lean
    CausalGeometry/Exchange/Quotient.lean
    CausalGeometry/Exchange/Laws.lean
    CausalGeometry/Exchange/Defect.lean
    CausalGeometry/Exchange/PairedTransport.lean
    CausalGeometry/Exchange/Observation.lean
    CausalGeometry/Exchange/Restriction.lean
    CausalGeometry/Exchange/Cost.lean
    CausalGeometry/Exchange/CoherenceCell.lean

Modelos en Models/, realizaciones fuente en Realization/, aritmetica especifica en Number/ o submodulo Exchange/Positive segun la auditoria de propietarios. No crear equivalentes de Quiver.Path, CategoryTheory.Functor, cocientes, TensorProduct u OreLocalization ya disponibles. Si falta una API nativa, documentar la ausencia en el pin y construir el minimo productor reutilizable.

Una estructura llamada GarsideData o RibbonData puede expresar hipotesis, pero su existencia no cierra el productor concreto. Los teoremas deben consumir construcciones, no concluir por proyeccion el campo que acaba de almacenar la conclusion.

Las nuevas estructuras no se añaden como campos opcionales a CausalNumber ni se imponen globalmente sobre EventSystem. Usar dominios y enriquecimientos relativos, con mapas de olvido demostrados. Distinguir una relacion Prop que permite cociente de los certificados Type que se conservan antes de tomarlo.

## 8. Incrementos y pruebas

I0 — Inventario y contratos. No exige modificar codigo historico. Publicar declaraciones reutilizadas, tipos y obligaciones pendientes reales.

I1 — Pasos y caminos causales. Probar las seis historias del modelo de tres eventos; extremos/contextos; dos rutas distinguibles. Gate autonomo.

I2 — Politicas y sectores. Congruencias, factor universal, YB no invertible, twin y recuperacion simetrica. Primer consumidor downstream puede avanzar con I1/I2.

I3 — Defectos y perdida. Omega, conjugacion, observadores y Phi/Psi. No depende de toda Garside.

I4 — Aritmetica. Positivo, perfiles, complementos, normalizador y Ore por etapas; preservar modelos clasicos anteriores.

I5 — Cocientes predictivos y restricciones. Invariancia contextual, costes y comparadores entre resoluciones.

I6 — Geometria y cierre. Mapas de complejos/Hodge, duales y ribbon solo en dominios probados; no fusionar sus gates.

D0–Dk — Consumidores ECIA. Cada uno registra productores exactos, contrato y evidencia de destino. No espera a I6 si usa solo I1–I3.

## 9. Recibo obligatorio de ejecucion

El esquema del recibo local debe incluir:

    schema_version
    campaign / increment / obligation_ids
    status_by_obligation
    source_repo / source_sha / source_dirty
    downstream_repo / downstream_sha (solo realizaciones)
    declared_pin / manifest_pin / resolved_dependency_sha
    lean_version / mathlib_revision
    command_argv / working_directory
    cpu_affinity / thread_limit / memory_limit
    input_parameters / seed / fixture_digest
    wall_time / peak_rss / exit_code
    certificate_bytes / proof_nodes_when_available
    stdout_digest / stderr_digest / retained_failure_paths
    declarations_checked / axioms_output / import_audit
    historical_consumers_checked
    reviewer_identity_and_scope
    limitations / unexecuted_checks

El runner real existente se inspecciona antes de extenderlo. No se publican comandos que aparenten existir si aun son rutas candidatas. No se añaden Actions ni CI. El recibo de planificacion y el recibo de compilacion son clases de evidencia distintas.

No borrar logs fallidos al repetir. Un cambio de source SHA exige explicar que evidencia sigue valida y cual debe repetirse. Una recompilacion parcial no se anuncia como validacion de todo el workspace. Un analisis por el autor no se presenta como revision independiente.

## 10. Comprobaciones realizadas al redactar este plan

En esta sesion se ejecutaron comprobaciones finitas independientes en Python para revisar las formulas de los controles propuestos:

* Hurwitz sobre S3: 216 triples verificaron la igualdad YB; 36 parejas verificaron conservacion del producto; se encontro una pareja no involutiva.
* R(x,y)=(y,y): los 8 triples de Bool verificaron YB.
* Las dos reflexiones sobre ZMod 5 son involutivas; las rutas sobre 0 dan 3 y 4.

Son comprobaciones de cordura de estos MODELOS FINITOS. No son teoremas Lean, no acreditan las presentaciones generales y no se han ejecutado aqui los gates del repositorio. Los resultados se pueden reproducir con el siguiente programa sin dependencias externas; es material de planificacion, no implementacion del nucleo causal:

```python
from itertools import permutations, product
P = list(permutations(range(3)))
def mul(a, b):
    return tuple(a[b[i]] for i in range(3))
def inv(a):
    return tuple(a.index(i) for i in range(3))
def H(a, b):
    return mul(mul(a, b), inv(a)), a
def r12(t, op):
    return (*op(t[0], t[1]), t[2])
def r23(t, op):
    return (t[0], *op(t[1], t[2]))
def yb(t, op):
    return r12(r23(r12(t, op), op), op) == r23(r12(r23(t, op), op), op)
assert all(yb(t, H) for t in product(P, repeat=3))
assert all(mul(*H(a, b)) == mul(a, b) for a, b in product(P, repeat=2))
assert any(H(*H(a, b)) != (a, b) for a, b in product(P, repeat=2))
assert all(yb(t, lambda a, b: (b, b)) for t in product([0, 1], repeat=3))
s1 = lambda m: (-m) % 5
s2 = lambda m: (2-m) % 5
assert all(s1(s1(m)) == m and s2(s2(m)) == m for m in range(5))
assert (s1(s2(s1(0))), s2(s1(s2(0)))) == (3, 4)
```

Esta lista no es una cifra agregada de tests del repositorio. La migracion de cada control a Lean y su interpretacion desde historias causales reales son obligaciones de CX04.
