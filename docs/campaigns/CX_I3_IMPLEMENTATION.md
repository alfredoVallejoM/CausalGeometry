# CX-I3 — Inversión formal, familias de leyes y defectos reversibles

Fecha: 2026-09-28. Rama de publicación: CausalGeometry/main.
Base exacta: 9148719564c2bc6463b95027669519d56c1367c3.
Código y manifiesto: a4073c5c5b070918b322e69a6f64ca459b4f6a8b.
Estado: SOURCE-WRITTEN / NON-KERNEL-PASS / LEAN-TYPECHECK-PENDING.
Filas nuevas acreditadas por el kernel: 0.

## 1. Alcance conservativo

Se continúa el fundamento causal de CX sin convertir ECIA en dependencia.
Todos los productores, tests, manifiestos y runners I1/I2 permanecen idénticos.
La raíz solo recibe cuatro imports; el índice documental recibe este enlace.
No se cambian EventSystem, CausalNumber, los pins, las otras ramas ni ECIA.
No se añaden workflows ni se modifica el runner global.

La inversión aquí es de transformaciones ENTRE historias. No deshace los
acontecimientos de la historia ni invierte la causalidad de EventSystem.
El constructor usado invierte todos los generadores del quiver cronológico
seleccionado. No se declara resuelta la localización selectiva de operaciones
causales arbitrarias.

## 2. Productor nativo de inversión

Exchange/Reversible.lean consume Quiver.FreeGroupoid del mathlib v4.32.1.
El archivo y las firmas se comprobaron mediante el conector en el pin exacto:

- FreeGroupoid.lean: 4e1115b66d22879fa5da370ca500488cbbbb4920.
- Core.lean: 87b752bd35da8616ca5cc628354e1795ec17f61b.
- Groupoid.lean: 968883bf434261867085174546fdf8e1fa52f17c.

No se implementa otra palabra firmada ni otro cociente en Lean. El constructor
nativo simetriza el quiver, forma caminos y toma su cociente de cancelación.
Sobre él se construye el funtor positive desde las rutas existentes y se
escriben las leyes de generadores, inversión, extensión y unicidad.

La igualdad positive ⋙ extend F = Paths.lift F garantiza que la extensión a
inversos coincide con la interpretación anterior en las rutas positivas.
Los mapas de quivers inducen funtores con identidad y composición. Los
prefijos y continuaciones causales ya construidos se extienden de ese modo.
Esto no acredita todavía todas las coherencias entre contextos de una
bicategoría completa de diarios.

## 3. Defecto reversible intrínseco

Exchange/Defect.lean fija explícitamente la convención de composición:
P ≫ Q significa primero P y después Q. Para P,Q:X->Y se define

    defect(P,Q) = P ≫ inv(Q),

es decir Q^-1 o P. Se escriben pruebas de:

    defect(P,Q)=id <=> P=Q;
    defect(Q,P)=inv(defect(P,Q));
    defect(a≫P≫b, a≫Q≫b)=a≫defect(P,Q)≫inv(a);
    F(defect(P,Q))=defect(F(P),F(Q)).

La tercera identidad distingue un cambio de presentación del defecto:
la modificación de la frontera final cancela; la inicial actúa por conjugación.
Una interpretación separadora prueba que el defecto fuente no es identidad.
Reflejar su trivialidad exige fidelidad local del funtor.

También se prueba que Phi≫Psi=id equivale a Psi=inv(Phi) en el dominio de
morfismos invertibles. Esto no afirma que todo par estructural sea así:
la igualdad sigue siendo una condición, no una consecuencia de que ambos
mapas sean individualmente invertibles. No se identifica la inversión con
restricción correlativa, dagger, adjunto ni curvatura geométrica.

## 4. Familias tipadas de leyes

Exchange/EquationFamily.lean introduce ParallelEquation como DATO: dos
morfismos paralelos con sus objetos fuente y destino. No contiene una prueba
que asuma su igualdad. Una familia indexada genera un HomRel nativo y su
cociente mediante la infraestructura I2.

Se demuestra el criterio preciso: un funtor respeta la familia si y solo si
iguala cada ecuación indexada, y en ese caso existe su descenso por el cociente.
Se añaden constructores de ecuaciones de cuadrados, ternarias, ida y vuelta
y comparación entre un generador contrario y el inverso formal. Unir dos
políticas exige respetar ambas por separado.

Esos constructores no son una declaración de que cualquier hexágono sea
Yang–Baxter. La identificación con una familia general de trenzas exige aún
construir sus diagramas causales y demostrar las leyes de todo el dominio.

## 5. La realización reversible conserva la diferencia ternaria

Models/ExchangeReversibleControls.lean reutiliza las seis historias y las
rutas 121/212 reales de I1. La realización de memoria se levanta a Core(Type):
cada generador lleva su isomorfismo y las pruebas de su inversa.

Se construye groupMemory(t), no solo un predicado que solicite su existencia.
La prueba positive_memory identifica su acción con la del observador I1 en
TODA ruta positiva. Para el parámetro 2, las rutas siguen observándose como
3 y 4 sobre el valor inicial 0. Por ello sus imágenes en el grupoide libre
son distintas y su defecto es no trivial.

Introducir inversos no ha impuesto Yang–Baxter. Las ecuaciones ternarias
siguen siendo una política adicional, que puede hacer descender o no una
interpretación.

El cociente de ese grupoide por la pareja ternaria conserva inversos y mata
exactamente el defecto especificado. Los observadores de esta familia que
descienden son exactamente t=0, también permitiendo isomorfismo natural en
el cuadrado de factorización. Para t!=0 no hay ese descenso compatible.

No se afirma que la observación finita sea fiel sobre todo el grupoide.

## 6. Generador contrario e inverso formal no son lo mismo

Se toman el intercambio positivo f:012->102 y el generador positivo distinto
g:102->012. Ambos proceden de diamantes reales. En el grupoide libre, g no se
identifica automáticamente con inv(f).

El separador es una realización reversible sobre los enteros que asigna
z -> z+1 a CADA generador positivo. Su inversa formal es z -> z-1. Por ello:

    counter(g)(0)=1;
    counter(inv(f))(0)=-1.

Esto prueba la desigualdad de esos morfismos con los mismos extremos.
Una realización de memoria por reflexiones puede identificar sus acciones;
no por ello la fuente libre los identifica.

Se construye después una familia explícita que impone g=inv(f). En su
cociente la ida y vuelta elegida sí cancela. Todas las memorias groupMemory(t)
respetan esa ley, pero la de t=2 sigue separando las rutas ternarias. Así se
prueba que imponer esta cancelación no impone la ecuación ternaria.

Al unir las dos políticas se vuelve a obtener el criterio exacto t=0.
El alcance es esta pareja de generadores y este hexágono causales, junto a la
API general de familias. No se anuncia aún el sector twin completo.

## 7. El cociente ternario tampoco es indiscreto

El contador reversible cuenta +1 en generadores positivos y -1 en inversos
formales. Respeta el par ternario de tres pasos, pero distingue una ruta de
tres intercambios de la ruta de cinco formada anteponiendo el viaje positivo
f;g. Esa ruta de ida y vuelta NO es f;inv(f) antes de imponer su ley adicional.

Así queda un control que refuta el colapso total incluso cuando ya existe
inversión formal. El control anterior con Nat de I2 no se reutiliza fuera de
su dominio irreversible: aquí se construye realmente el destino Int invertible.

## 8. Validación ejecutada y límites

Se ejecutó primero la suite I2: 48 tests pasaron antes de añadir código.
La suite I3 suma 23 tests: 18 controles finitos y 5 contratos de fuente.
Pasan los 71 tests, incluida la repetición de los 48 anteriores sin modificar
su código. La vista histórica proyecta solo los cuatro imports nuevos después
de verificar el hash exacto del prefijo; los productores son enlaces a los
archivos actuales. Se conserva también la proyección I2->I1 ya validada.

El modelo finito usa seis historias, doce generadores positivos dirigidos y
24 flechas firmadas. El corpus de longitud 0..4 contiene 2046 caminos firmados.
Comprueba extremos, inversos, cancelaciones, reducción, conjugación de defectos,
observadores, diferencia entre generador contrario e inverso, y las fronteras
entre las políticas. Es un modelo de palabras firmado explícito; no es un
teorema que clasifique todos los testigos Exchange.Step de Lean.

Se comprobó sintaxis Python, verificador no-kernel (salida 3), ausencia real de
Lean/Lake (salida 3), manifiesto ausente (salida 1) y hash incorrecto (salida 1).
Ningún compilador fue simulado. La prueba de acceso a GitHub desde el runtime
falló por DNS; el conector sí permite leer y publicar fuentes.

No se ejecutó Lean: los 38 nuevos #print axioms, más los 22 y 36 históricos,
siguen pendientes. Tampoco se ejecutaron auditoría global de imports,
workspace completo o consumidores ECIA. No se atribuye revisión independiente
a este trabajo del autor con modelos y controles de fuente.

El trabajo local parte de los ZIP I1/I2 montados. No se afirma que sea un
checkout completo hidratado. Los hashes del payload se contrastan y se
conservan en verification/cx-i3/manifest.json.

## 9. Gate actual

    python3 tools/verify_cx_i3.py --plan
    python3 tools/verify_cx_i3.py

Solo controles no-kernel:

    python3 tools/verify_cx_i3.py --non-kernel

El último comando devuelve 3 aunque pasen los tests. El gate completo compila
los nuevos módulos y consumidores históricos, ejecuta los tres arneses y
verifica las 22+36+38 salidas reales de axiomas con el comprobador I2 reutilizado.
No modifica los verificadores anteriores ni sus manifiestos inmutables.
Se limita a dos CPU disponibles y registra comandos, logs, tiempos, RSS
acumulado de hijos, hashes y dependencia resuelta.

## 10. Complejidad y continuación

La construcción formal nativa de un cociente no es un normalizador ejecutable
ni una cota de resolución del problema de palabras. La inclusión positiva
recorre el camino; los certificados y contextos permanecen parte del coste.

El normalizador del modelo Python usa una pila de letras con identidad de
arista y signo: O(ell) operaciones de pila y O(ell) memoria para palabras de
ell letras, con endpoints de tamaño fijo tres. Esta cota NO se anuncia para
todas las presentaciones ni como un teorema del normalizador Lean inexistente.
Al variar la longitud de historia h, copiar/comparar extremos cuesta O(h) con
esta representación, y la cota se multiplica por ese coste.

La enumeración tiene hasta 6*4^ell caminos por longitud: se mantiene acotada,
no se vende como algoritmo eficiente para entradas generales. El coste
bit de los enteros y el tamaño de las evidencias se registran por separado.

Siguiente frontera: elaborar y reparar el cono acumulado, construir la
involución de los generadores causales y las familias de leyes para todos
los diagramas admitidos; demostrar las coherencias de contexto requeridas,
y desarrollar el sector Yang–Baxter no invertible por su propia ruta.
La localización selectiva, acciones braid/twin/cactus generales, cálculo
trenzado, coherencias superiores y ECIA siguen siendo obligaciones separadas.

## 11. Publicación y reproducción

La auditoría de blobs contrastó los archivos fuente con los publicados.
Una diferencia de indentación en el docstring del nuevo test se sincronizó
y se repitió el gate completo no-kernel: 71 tests PASS. No cambió ninguna
ley ni productor matemático. La evidencia de ambos ensayos se conserva.

El repositorio contiene `verification/cx-i3/test-summary.txt`, el manifiesto
y la validación con los hashes de las evidencias. El ZIP de entrega conserva
los logs originales, recibos y pruebas de rechazo, tanto descomprimidos como
en evidence.tar.gz. El archivo de validación distingue esta ejecución local
sobre los ZIP montados de una compilación en un checkout hidratado.
