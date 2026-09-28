# CX-I2 — Cocientes de coherencia y descenso de observadores

Fecha: 2026-09-28. Rama de destino: CausalGeometry/main.
Base: c517fcc282c748d51d54151f1c1b8035c61b2f6c.
Código, tests, arnés y manifiesto: 836d975bbd0547b8519cd37b5035ac53ea652a3e.
Estado: SOURCE-WRITTEN / 48 NON-KERNEL TESTS PASS / LEAN-TYPECHECK-PENDING.
Nuevas filas acreditadas: 0.

## 1. Alcance y conservación

CX-I2 continúa sobre las rutas causales de CX-I1; no modifica sus productores,
tests, runner ni manifiesto. La única modificación de su payload es añadir
tres imports al final de CausalGeometry.lean, conservando exactamente todos
los bytes anteriores. No se cambia EventSystem, CausalNumber, los pins de
Lean/mathlib, las otras ramas, el runner global ni GenContinuum. No hay Actions.

Los tres módulos nuevos son:

- Exchange/Quotient.lean: cociente nativo, congruencia generada, criterio de
  descenso estricto y hasta isomorfismo natural, comparación entre cocientes.
- Exchange/ContextRelation.lean: ecuaciones estables bajo contextos de historias
  causales, su saturación por congruencia y los funtores de contexto descendidos.
- Models/ExchangeCoherenceControls.lean: cociente de la pareja ternaria de CX-I1,
  clasificación de todos los observadores de parámetro t en ZMod 5 y un control
  que prueba que el cociente no identifica todas las rutas paralelas.

Las pruebas se han escrito, pero todavía no se han elaborado con Lean.
No se atribuye la validación de los modelos Python al kernel.

## 2. Cociente real, no una propiedad universal recibida como campo

Se reutilizan CategoryTheory.Quotient, Quotient.functor, Quotient.lift,
Quotient.lift_unique y Quotient.functor_map_eq_iff. Sus firmas se leyeron en
mathlib v4.32.1, blob f91fb662557a3f68d5a366f5c95422b7ae4048e2.

Dada una relación r sobre morfismos paralelos, Generated r se define como
la relación de igualdad inducida por el funtor del cociente. El teorema
`generated_iff` la identifica con EqvGen(CompClosure r). De ahí se conserva la
construcción nativa, sin crear otra categoría de cocientes ni una segunda
noción de congruencia.

La API construye `descend r F h` cuando F respeta los generadores y demuestra:

    F respeta r <=> existe G con q_r ⋙ G = F.

También demuestra unicidad del G con ese cuadrado, propagación del respeto a
la congruencia generada y minimalidad frente a cualquier congruencia que
contenga r. Para r incluida en s se construye Q(r) -> Q(s), con leyes de
identidad y composición. Más relaciones significan más identificaciones,
no una inclusión fiel de información.

Una observación que respeta r y distingue dos morfismos demuestra que esos
morfismos siguen siendo distintos en el cociente. Es un certificado de
separación; no se requiere decidir toda igualdad de una presentación.

## 3. No confundir los dos tipos de contexto

Componer otra RUTA de intercambios antes o después de P no es lo mismo que
anteponer o añadir EVENTOS a las dos HISTORIAS relacionadas por P.

El cociente nativo cierra las relaciones bajo composición de rutas. Para el
segundo problema se construye ContextClosure K sobre una familia K(C,D) de
relaciones, usando los prefixFunctor/suffixFunctor causales ya construidos.
Después se aplica la saturación nativa en cada categoría de historias.

Se escriben pruebas de:

- cierre por contextos de la familia construida;
- minimalidad de ContextClosure;
- estabilidad contextual de toda la congruencia saturada;
- minimalidad entre familias de congruencias contextuales;
- monotonía respecto de la familia de ecuaciones;
- funtores prefixOnQuotient y suffixOnQuotient y sus cuadrados con la proyección.

Esto no es todavía toda la bicategoría de diarios ni todas sus coherencias.
Tampoco impone automáticamente la ecuación ternaria en cada dominio causal.

## 4. Control conectado a CX-I1: exactamente t=0 desciende

Se reutilizan sin modificación:

    P: 012 -> 102 -> 120 -> 210
    Q: 012 -> 021 -> 201 -> 210.

TernaryEquation tiene UN generador: P=Q. El cociente local aplica la clausura
nativa por composición de rutas. La infraestructura contextual general del
apartado anterior es independiente; este control local no se presenta como
una prueba de todas las relaciones braid, twin o symmetric.

Para el observador memory(t) existente:

    memory(t)(P)(m) = -t-m
    memory(t)(Q)(m) = 2t-m.

Respetar el generador obliga a -t=2t en ZMod 5, es decir 3t=0, y por tanto t=0.
El sentido contrario consume el control zero_offset_forgets de CX-I1.

Se construye descendedZero y su cuadrado. El resultado central escrito es:

    (existe F con projection ⋙ F = memory(t)) <=> t=0.

No es solo un resultado para t=2: clasifica todos los parámetros de esta
familia. La fuente libre sigue teniendo P distinto de Q; la proyección los
identifica por una ecuación declarada.

## 5. La obstrucción no desaparece cambiando de presentación

La API incluye:

    F respeta r
      <=> existe G con un isomorfismo natural q_r ⋙ G ~= F.

El sentido no trivial usa naturalidad y cancelación por una componente
invertible. No se supone igualdad definicional de las realizaciones.

En el modelo también se escribe:

    (existe G con projection ⋙ G ~= memory(t)) <=> t=0.

Por tanto offset_two_no_factor_upToIso excluye recuperar el observador de
parámetro dos incluso permitiendo esa comparación por isomorfismo natural.
No se confunde este resultado con comparadores de dimensión superior más
generales que no se han construido.

## 6. El cociente no borra todas las transformaciones

Además de P y Q se construye una ruta de cinco intercambios: un viaje de ida
y vuelta de dos pasos seguido de P. Conserva los mismos extremos.

Un segundo intérprete suma uno por intercambio. Respeta P=Q porque ambos
contienen tres pasos, pero distingue la ruta de tres de la de cinco.

`longerRoute_not_identified` utiliza ese observador y la propiedad de descenso
para impedir el colapso total del hom-set. No se han añadido relaciones de
cancelación inversa: un viaje de ida y vuelta no es identidad solo porque
cada acción elemental de otro observador sea involutiva.

Con NoEquation, la pareja P,Q permanece distinta. El control distingue
fuente libre, cociente generado y mutación que identifica todo.

## 7. Ejecución y evidencia

48 tests no-kernel pasan:

- 16 controles nuevos de modelo finito;
- 7 contratos nuevos de conservación/reutilización;
- los 25 tests originales de CX-I1, sin cambiar su código.

El test histórico que exige la raíz exacta de I1 se ejecuta sobre una vista
explícita que proyecta SOLO los tres imports nuevos. Primero se comprueba el
hash del prefijo; los productores son enlaces a los archivos actuales, no
copias históricas. El nuevo test verifica la raíz completa y todos los hashes
del payload I1. No se ha relajado ni eliminado una prueba para aceptar cambios.

El primer ensayo dio 47 éxitos y un fallo: una expectativa auxiliar pedía más
de 100 aplicaciones de la relación. La enumeración contiene exactamente 98,
con cuenta independiente sum((n-2)*2^(n-2), n=3..6). Se sustituyó el umbral por
esa igualdad exacta; no se cambió ninguna relación ni productor. El log fallido
queda conservado junto al posterior.

El corpus recorre 762 palabras con seis historias de inicio y longitudes 0..6,
y comprueba 14 400 pares de renombrados biyectivos de fronteras de la fibra.
Son escenarios dentro de tests finitos, no miles de teoremas Lean. El modelo de
palabras no es un teorema de clasificación de todos los certificados Step.

Se ejecutaron también sintaxis Python, verificador no-kernel (salida 3),
detección real de toolchain ausente (salida 3) y rechazo de manifiesto ausente
o hash incorrecto (salida 1). No se simuló un compilador.

Lean/Lake siguen ausentes; el intento de acceso de red no resolvió github.com.
No se ejecutaron la elaboración, las 22+36 salidas reales de axiomas, la
auditoría global de fuentes/imports, el workspace completo ni ECIA.

El trabajo local partió del ZIP montado de CX-I1. Los ocho blobs nuevos o
modificados del commit fuente se contrastaron byte a byte por su hash Git
con los archivos usados en los controles. No se afirma disponer de un
checkout completo hidratado ni de una revisión independiente.

El repositorio conserva `verification/cx-i2/tests.log` y `validation.json`.
El ZIP del incremento contiene todos los logs sin comprimir, incluido el
primer fallo y los recibos originales de las ejecuciones. Sus hashes quedan
registrados en `validation.json`; no se atribuyen a un checkout hidratado.

## 8. Gate local y compatibilidad con la evidencia anterior

En el checkout actualizado:

```bash
python3 tools/verify_cx_i2.py --plan
python3 tools/verify_cx_i2.py
```

Para solo los controles independientes:

```bash
python3 tools/verify_cx_i2.py --non-kernel
```

El modo no-kernel devuelve 3 aunque los tests pasen. El gate completo exige
Lean real, valida los hashes, reutiliza source_audit.py, compila el cono de
CX-I2 y los consumidores variacionales anteriores y ejecuta ambos arneses.
Exige 22 y 36 salidas axiomáticas reales, no solo ausencia textual de atajos.
Registra versiones, dependencia resuelta, afinidad máxima de dos CPU, logs,
tiempos y RSS acumulado de hijos. Su éxito no acredita todo el programa.

El runner y manifiesto I1 son evidencia inmutable de su SHA. Su comprobación
exacta de raíz no corresponde al nuevo agregado. Para la raíz actual se usa
el runner I2, que comprueba explícitamente la migración; no se reescribe el
manifiesto antiguo para aparentar una validación histórica.

## 9. Complejidad y frontera siguiente

El cociente formal no enumera representantes. No se ha construido un
normalizador ni un algoritmo general para decidir las nuevas congruencias.

En el modelo finito de palabras de longitud ell hay 2^ell palabras por inicio.
Buscar ventanas y copiar candidatos cuesta hasta O(ell^2 * 2^ell) con tuplas
y el algoritmo ingenuo descrito, sin considerar el cache global de varias
longitudes. El corpus usa longitudes acotadas; no es una afirmación de HPC.
Una búsqueda con presupuesto que no encuentra prueba devuelve INCONCLUSIVE,
no desigualdad. La separación por el contador es un argumento diferente.

Tras elaborar y corregir I1/I2, el siguiente trabajo fuente es construir las
familias generales de leyes de intercambio e inversos y sus comparadores:
no confundir la ecuación local probada aquí con toda una presentación de
trenzas. También quedan las coherencias entre contextos, los defectos Phi/Psi,
la teoría predictiva completa y las realizaciones ECIA. Ninguno se da por
cerrado mediante este control.
