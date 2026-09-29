# CX-I7 — Dominios persistentes de compatibilidad causal

Fecha: 2026-09-29. Repositorio/ramal: CausalGeometry/main.
Base: 8ee861b695c774ff1ea4425f8a55f5f1f23e53f4.
Código/manifiesto: 8f96161174f3b43e804e89cb313892040a0509be.
Estado: SOURCE-WRITTEN / 192 NON-KERNEL TESTS PASS / LEAN-TYPECHECK-PENDING.
Filas nuevas acreditadas: 0. No se modifica ECIA ni GenContinuum.

## 1. Problema y alcance

I6 construyó el núcleo de un defecto puntual y mostró que no tiene por qué
ser invariante. I7 construye el mayor dominio que continúa siendo compatible
bajo todas las continuaciones admitidas. No supone naturalidad del transporte,
Yang–Baxter, inversos, dimensión finita ni adjunción para definirlo.

La construcción abstracta sirve para cualquier categoría de procesos y dos
funtores lineales sobre ella. La instancia concreta de este incremento usa
la categoría EXISTENTE de intercambios entre historias con fronteras U,V
fijas. Sus continuaciones son rutas adicionales de intercambios. Añadir
acontecimientos, cambiar fronteras o imponer todos los contextos entre
fronteras es una extensión distinta, aún no afirmada por este incremento.

Cinco módulos nuevos:

- Calculus/LinearInvariantCore: interior invariante de restricciones, maximalidad,
  monotonía, idempotencia y un funtor restringido con inclusión natural.
- Calculus/PersistentLinearCompatibility: dominio de anulación de TODOS los
  defectos futuros y transporte natural construido sobre ese dominio.
- Calculus/LinearInvariantPaths: criterio mediante generadores, refinamientos
  por horizontes y un criterio exacto de parada global.
- Exchange/PersistentCompatibility: consumo de las acciones causales y defectos
  de I6, Phi/Psi independientes, estados básicos y estados constantes.
- Models/ExchangePersistentControls: subdominio propio no nulo, fallo retardado
  y control de cancelación entre transportes sucesivos.

EventSystem, PairedTransform, CausalNumber, los módulos I1–I6, sus manifiestos,
tests y runners permanecen intactos. La raíz añade cinco imports; no se cambia
ningún pin, rama ajena, workflow o runner global.

## 2. Interior invariante, no un núcleo puntual promovido

Para F:C->ModuleCat(K) y una familia L(X) de submódulos, se construye

    Core_F(L)(X) = {x | para todo r:X->Y, F(r)x pertenece a L(Y)}.

La identidad da Core_F(L)(X) <= L(X). La composición prueba estabilidad.
Toda familia estable M contenida en L está contenida en Core_F(L). Se escriben
además monotonía, Core(Core(L))=Core(L), y el criterio L estable si y solo si
Core(L)=L. Se construyen los mapas restringidos como mapas lineales reales,
sus leyes functoriales y la inclusión natural en F. No se introduce una
segunda categoría o una estructura que reciba la maximalidad como campo.

## 3. Compatibilidad persistente y reparación de naturalidad

Para F,G y mapas por objeto tau_X sin ley de naturalidad asumida:

    D_r = G(r) tau_X - tau_Y F(r),
    P(X) = intersección, para todos r:X->Y, de ker D_r.

El cuadrado defectuoso es el productor LinearSquare.defect de I6.

La clave de estabilidad no es que un defecto aislado sea cero: si x está en
P(X), tanto D_r(x) como D_(r;t)(x) son cero para cualquier continuación t.
La ley de composición obliga a D_t(F(r)x)=0. Así F(r)x pertenece a P(Y).

Sobre P se construye una transformación natural P-restricted(F)->G. No se
concluye que sea invertible, fiel o adjunta. Tampoco se transforma el dominio
en una nueva primitiva ontológica.

## 4. Criterio local exacto

En la categoría nativa de caminos de un quiver, sea

    L(X) = intersección de ker D_s para todos los generadores salientes s.

Se escribe el teorema

    P(X) = Core_F(L)(X).

La demostración consume las rutas generadas, su composición y las acciones
existentes. Distingue estabilidad por rutas de una comprobación local sin
estabilidad. Por eso no basta que todos los intercambios inmediatos acepten x.

En la especialización causal, tanto la posición como la admisibilidad del
paso proceden de Exchange.Step. No se reemplaza la fuente por una palabra
posicional de Artin para definir el dominio.

## 5. Control de fallo después de dos pasos

Se reutilizan h012, h102, h120 y middleState=[false,true,false]. La fuente
observa con flip. El destino usa wakeZero: coincide con flip salvo que envía
(false,false) a (true,true).

Los dos intercambios iniciales admisibles ven pares distintos de (false,false),
por lo que ambos cuadrados con coeficientes identidad conmutan sobre ese
estado. Se escribe la prueba para todo Step saliente, usando su cota de
posición: solo puede ser cero o uno.

Pero la ruta causal

    012 -> 102 -> 120

primero lleva el estado a [true,false,false]. El siguiente intercambio actúa
sobre el par final (false,false): la fuente conserva [true,false,false] y el
destino produce [true,true,true]. La base libre distingue ambos. Por tanto
ese estado está en todos los núcleos locales iniciales, pero no en P(h012).

## 6. El dominio útil no tiene por qué ser cero o todo

Se prueba que un operador que fija (a,a) conserva la fibra constante a en
cualquier longitud y cualquier ruta causal admitida. Si los dos operadores
fijan (a,a) y (f(a),f(a)), su vector básico constante pertenece a P.

Para flip y copyRight, id:Bool->Bool, el vector básico de [false,false,false]
es persistente y no nulo. El estado [false,true,false] falla sobre la route121
anterior. Esto da una prueba escrita de que P(h012) no es bottom ni top.

La enumeración racional independiente del modelo de seis historias y ocho
estados por fibra obtiene:

| Fuente/destino | Dimensión local | Dimensión persistente | Rondas hasta certificado |
|---|---:|---:|---:|
| flip/copyRight | 2 | 2 | 1 |
| flip/toggleFirst | 1 | 1 | 1 |
| flip/wakeZero | 5 | 4 | 2 |

Las dimensiones son resultados del oráculo finito ejecutado; no se presentan
como teoremas Lean de clasificación de todos los certificados Step.

El segundo ejemplo muestra otra frontera: ningún vector básico individual
es compatible, pero la suma uniforme de los ocho básicos sí lo es. Por tanto
la compatibilidad lineal no equivale a seleccionar los estados compatibles.
La API solo prueba span(básicos compatibles) <= P, no igualdad universal.
No hay interpretación probabilística ni superposición física asumidas.

## 7. Composición y pérdida

Para transportes tau:F->G y sigma:G->H se obtiene el dominio seguro

    P_tau(X) intersect tau_X^(-1)(P_sigma(X)) <= P_(sigma tau)(X).

La inclusión puede ser estricta: el control de I6 tiene defectos direccionales
no nulos que cancelan al componer. Se conserva ese contraejemplo ahora como
una comparación de dominios. Phi/Psi tienen sus dos fórmulas separadas y no
se infiere que el recorrido sea identidad.

Si se añade una observación natural sigma:G->H, el dominio compatible puede
crecer porque sigma borra defectos. Esa inclusión se demuestra, sin afirmar
que todo crecimiento sea una mejora de fidelidad. El control de colapso a
un singleton produce dominio total y no recupera la información original.

## 8. Horizontes y parada certificada

Se define la sucesión de familias

    K_0(X)=L(X),
    K_(n+1)(X)=L(X) intersect intersección_s F(s)^(-1)(K_n(target(s))).

Se escriben pruebas de descenso y de Core(L)<=K_n en todo horizonte.
Si K_(n+1)=K_n en TODOS los objetos, K_n es estable y maximal, porque procede
de esa iteración superior. El teorema horizon_fixed_eq_core da la igualdad
con Core(L). No se infiere maximalidad de un punto fijo arbitrario: bottom
puede ser estable y estar muy por debajo del mayor dominio.

El oráculo finito de los tests implementa esta recurrencia por espacios de
filas racionales y preimágenes, sin enumerar las rutas para resolverla. Hay
una segunda comprobación independiente por palabras cortas para verificar
la fórmula de horizonte en el modelo acotado. Un presupuesto agotado devuelve
INCONCLUSIVE con una aproximación EXTERIOR. Que un único vértice deje de
cambiar no basta: se conserva un control de tres vértices que lo refuta.

## 9. Complejidad y límites

Para un grafo FINITO explícito, dimensiones d_p finitas, matrices racionales
exactas y refinamiento simultáneo, el total de dimensiones disminuye en cada
pasada no estacionaria. Hay a lo sumo sum_p d_p - rango_inicial_total pasadas
estrictas, más una pasada que confirma estacionariedad. Este razonamiento y
los controles finitos no son una prueba Lean de terminación universal.

Representando K_n(p) como núcleo de una base reducida C_n(p), cada arista
p->q añade C_n(q) A_s a las restricciones en p. Si r_q es el número de filas,
ese producto denso cuesta O(r_q d_q d_p) operaciones de campo. Reducir R_p
filas de ancho d_p cuesta O(R_p d_p^2) con la eliminación usada. Se contabilizan
las matrices de las aristas, las bases actuales/siguientes y los racionales;
el crecimiento de bits no se considera constante ni se ha acotado globalmente.

El productor Lean general cuantifica sobre continuaciones; no enumera todos
los representantes ni proporciona por sí solo un algoritmo efectivo. Si hay
infinitas historias, campos no computables o dimensión infinita, la cota
finita anterior no se aplica. Las seis historias del control no justifican
materializar h! historias para una entrada causal general.

## 10. Evidencia y ejecución

Se ejecutó la suite I6: 159 PASS. La suite nueva pasa 192: 24 tests exactos
finitos, 9 contratos de fuente y los 159 anteriores sin modificar su código.
La proyección de raíz histórica elimina exactamente el sufijo declarado y
contrasta el hash; los archivos productores son los actuales.

Se ejecutaron sintaxis Python, modo no-kernel (salida 3), falta real de
Lean/Lake (salida 3), y rechazo de manifiesto ausente/hash alterado (salida 1).
Lean y Lake no existen en el entorno; curl no pudo resolver github.com.
No se simula el compilador. Los 52 comandos nuevos de axiomas, 304 acumulados,
siguen pendientes de ejecución real, junto con la auditoría global, workspace
completo y cualquier consumidor ECIA.

El contexto local son los ZIP I1–I6 montados; no es un checkout completo.
La procedencia se contrasta mediante hashes de blobs remotos. Los recibos de
ejecución retienen source_sha=null. Un Git auxiliar para comprobar parches
no se utiliza como evidencia de ejecución desde el commit remoto.

Gate para el checkout actualizado:

    python3 tools/verify_cx_i7.py --plan
    python3 tools/verify_cx_i7.py

Solo controles independientes:

    python3 tools/verify_cx_i7.py --non-kernel

## 11. Frontera pendiente

El alcance requiere elaboración y corrección en Lean antes de acreditarse.
La futura estabilidad al añadir eventos/cambiar fronteras necesita sus mapas
y comparadores de contexto; no se deduce del resultado de frontera fija.
También siguen pendientes los cocientes predictivos completos, la teoría
conjunta de restricciones/levantamientos, Garside/cactus y consumidores ECIA.
Esta entrega no cambia el ledger histórico ni sustituye aquellas obligaciones.
