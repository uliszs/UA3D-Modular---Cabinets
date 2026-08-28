import tkinter as tk
from tkinter import simpledialog, messagebox, filedialog
import math
import json
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Dict, Tuple

# ============================================================
# UA3D Modular - Gabinetes
# Versión 1.0
# Desarrollado por Ulises Alvarado
# Arquitecto & Artista 3D
# ============================================================

COLOR_PUERTA = "#d9a066"

# ------------------------------------------------------------------
# EXPORTADORES (OBJ / STL / DXF)
# ------------------------------------------------------------------
def exportar_obj(app, factor, ruta):
    vertices = []
    caras = []
    for panel in app._generar_paneles():
        x0, y0, z0, x1, y1, z1 = panel["caja"]
        for verts, _normal in app._caras_caja(x0, y0, z0, x1, y1, z1):
            base = len(vertices) + 1
            vertices.extend((x * factor, -z * factor, y * factor) for x, y, z in verts)
            caras.append((base, base + 1, base + 2))
            caras.append((base, base + 2, base + 3))

    with open(ruta, "w") as f:
        f.write("# Cabinet exported from UA3D Modular - Cabinets (units: per scale factor)\n")
        for x, y, z in vertices:
            f.write(f"v {x:.4f} {y:.4f} {z:.4f}\n")
        for cara in caras:
            f.write("f " + " ".join(str(i) for i in cara) + "\n")


def exportar_stl(app, factor, ruta):
    with open(ruta, "w") as f:
        f.write("solid cabinet\n")
        for panel in app._generar_paneles():
            x0, y0, z0, x1, y1, z1 = panel["caja"]
            for verts, normal in app._caras_caja(x0, y0, z0, x1, y1, z1):
                nx, ny, nz = normal
                rot_normal = (nx * factor, -nz * factor, ny * factor)
                rot_verts = [(vx * factor, -vz * factor, vy * factor) for vx, vy, vz in verts]
                for tri in (rot_verts[0:3], (rot_verts[0], rot_verts[2], rot_verts[3])):
                    f.write(f"facet normal {rot_normal[0]:.4f} {rot_normal[1]:.4f} {rot_normal[2]:.4f}\n")
                    f.write("  outer loop\n")
                    for vx, vy, vz in tri:
                        f.write(f"    vertex {vx:.4f} {vy:.4f} {vz:.4f}\n")
                    f.write("  endloop\nendfacet\n")
        f.write("endsolid cabinet\n")


def _fusionar_intervalos(intervalos):
    intervalos = sorted(intervalos)
    out = []
    for s, e in intervalos:
        if out and s <= out[-1][1] + 1e-6:
            out[-1] = (out[-1][0], max(out[-1][1], e))
        else:
            out.append((s, e))
    return out


def _merge_edges(edges):
    horiz = defaultdict(list)
    vert = defaultdict(list)
    for (xa, ya), (xb, yb) in edges:
        if abs(ya - yb) < 1e-6 and abs(xa - xb) > 1e-6:
            horiz[round(ya, 4)].append((min(xa, xb), max(xa, xb)))
        elif abs(xa - xb) < 1e-6 and abs(ya - yb) > 1e-6:
            vert[round(xa, 4)].append((min(ya, yb), max(ya, yb)))

    resultado = []
    for y, intervalos in horiz.items():
        for x0, x1 in _fusionar_intervalos(intervalos):
            resultado.append(((x0, y), (x1, y)))
    for x, intervalos in vert.items():
        for y0, y1 in _fusionar_intervalos(intervalos):
            resultado.append(((x, y0), (x, y1)))
    return resultado


def _union_edges(rects):
    rects = [(round(x0, 4), round(y0, 4), round(x1, 4), round(y1, 4))
             for x0, y0, x1, y1 in rects if x1 > x0 and y1 > y0]
    if not rects:
        return []
    xs = sorted(set(v for r in rects for v in (r[0], r[2])))
    ys = sorted(set(v for r in rects for v in (r[1], r[3])))
    if len(xs) < 2 or len(ys) < 2:
        return []
    xi = {v: i for i, v in enumerate(xs)}
    yi = {v: i for i, v in enumerate(ys)}
    nx, ny = len(xs) - 1, len(ys) - 1
    filled = [[False] * nx for _ in range(ny)]
    for x0, y0, x1, y1 in rects:
        i0, i1 = xi[x0], xi[x1]
        j0, j1 = yi[y0], yi[y1]
        for j in range(j0, j1):
            row = filled[j]
            for i in range(i0, i1):
                row[i] = True

    edges = []
    for j in range(ny):
        for i in range(nx):
            if not filled[j][i]:
                continue
            x0, x1 = xs[i], xs[i + 1]
            y0, y1 = ys[j], ys[j + 1]
            if i == 0 or not filled[j][i - 1]:
                edges.append(((x0, y0), (x0, y1)))
            if i == nx - 1 or not filled[j][i + 1]:
                edges.append(((x1, y0), (x1, y1)))
            if j == 0 or not filled[j - 1][i]:
                edges.append(((x0, y0), (x1, y0)))
            if j == ny - 1 or not filled[j + 1][i]:
                edges.append(((x0, y1), (x1, y1)))
    return _merge_edges(edges)


class _LienzoDXF:
    def __init__(self, scale, altura_texto_cota, altura_texto_titulo,
                 offset_cota, offset_cota_extra, tick_size):
        self.scale = scale
        self.altura_texto_cota = altura_texto_cota
        self.altura_texto_titulo = altura_texto_titulo
        self.offset_cota = offset_cota
        self.offset_cota_extra = offset_cota_extra
        self.tick_size = tick_size
        self.lineas_mueble = []
        self.lineas_cotas = []
        self.textos_cotas = []
        self.textos_titulos = []

    def cota(self, x1, y1, x2, y2, off_dx, off_dy, texto):
        ox1, oy1 = x1 + off_dx, y1 + off_dy
        ox2, oy2 = x2 + off_dx, y2 + off_dy
        self.lineas_cotas.append((x1, y1, ox1, oy1))
        self.lineas_cotas.append((x2, y2, ox2, oy2))
        self.lineas_cotas.append((ox1, oy1, ox2, oy2))

        largo = math.hypot(ox2 - ox1, oy2 - oy1) or 1.0
        dx, dy = (ox2 - ox1) / largo, (oy2 - oy1) / largo
        ang = math.radians(45)
        tx = dx * math.cos(ang) - dy * math.sin(ang)
        ty = dx * math.sin(ang) + dy * math.cos(ang)
        half = self.tick_size / 2
        for px, py in [(ox1, oy1), (ox2, oy2)]:
            self.lineas_cotas.append((px - tx * half, py - ty * half,
                                       px + tx * half, py + ty * half))

        mx, my = (ox1 + ox2) / 2, (oy1 + oy2) / 2
        mag = math.hypot(off_dx, off_dy) or 1.0
        nx, ny = off_dx / mag, off_dy / mag
        self.textos_cotas.append((mx + nx * 0.12, my + ny * 0.12, texto, self.altura_texto_cota))

    def fila_cotas(self, divisiones, transform, off_dx, off_dy):
        tramos = [(a, b) for a, b in zip(divisiones, divisiones[1:]) if abs(b - a) >= 0.1]
        for c1, c2 in tramos:
            x1, y1 = transform(c1)
            x2, y2 = transform(c2)
            self.cota(x1, y1, x2, y2, off_dx, off_dy, f"{(c2 - c1) * self.scale:.2f} m")
        if len(tramos) > 1:
            c1, c2 = divisiones[0], divisiones[-1]
            x1, y1 = transform(c1)
            x2, y2 = transform(c2)
            f_gen = (self.offset_cota + self.offset_cota_extra) / self.offset_cota
            self.cota(x1, y1, x2, y2, off_dx * f_gen, off_dy * f_gen,
                      f"{(c2 - c1) * self.scale:.2f} m")

    def escribir(self, ruta):
        with open(ruta, "w", encoding="ascii", errors="ignore") as f:
            # HEADER: declara la versión del formato (sin esto, AutoCAD
            # a veces se queda en el prompt "Press ENTER to continue").
            f.write("0\nSECTION\n2\nHEADER\n")
            f.write("9\n$ACADVER\n1\nAC1009\n")
            f.write("9\n$INSUNITS\n70\n6\n")
            f.write("0\nENDSEC\n")

            f.write("0\nSECTION\n2\nTABLES\n")
            # LTYPE: la capa referencia el linetype CONTINUOUS por nombre;
            # AutoCAD lo exige declarado explícitamente en la tabla.
            f.write("0\nTABLE\n2\nLTYPE\n70\n1\n")
            f.write("0\nLTYPE\n2\nCONTINUOUS\n70\n0\n3\nSolid line\n72\n65\n73\n0\n40\n0.0\n")
            f.write("0\nENDTAB\n")

            f.write("0\nTABLE\n2\nLAYER\n70\n2\n")
            f.write("0\nLAYER\n2\nCABINET\n70\n0\n62\n7\n6\nCONTINUOUS\n")
            f.write("0\nLAYER\n2\nDIMENSIONS\n70\n0\n62\n8\n6\nCONTINUOUS\n")
            f.write("0\nENDTAB\n")
            f.write("0\nENDSEC\n")

            # BLOCKS: AutoCAD espera encontrar esta sección aunque esté vacía.
            f.write("0\nSECTION\n2\nBLOCKS\n0\nENDSEC\n")

            f.write("0\nSECTION\n2\nENTITIES\n")
            for x1, y1, x2, y2 in self.lineas_mueble:
                f.write("0\nLINE\n8\nCABINET\n")
                f.write(f"10\n{x1:.4f}\n20\n{y1:.4f}\n30\n0.0\n")
                f.write(f"11\n{x2:.4f}\n21\n{y2:.4f}\n31\n0.0\n")
            for x1, y1, x2, y2 in self.lineas_cotas:
                f.write("0\nLINE\n8\nDIMENSIONS\n")
                f.write(f"10\n{x1:.4f}\n20\n{y1:.4f}\n30\n0.0\n")
                f.write(f"11\n{x2:.4f}\n21\n{y2:.4f}\n31\n0.0\n")
            for x, y, texto, altura in self.textos_titulos + self.textos_cotas:
                f.write("0\nTEXT\n8\nDIMENSIONS\n")
                f.write(f"10\n{x:.4f}\n20\n{y:.4f}\n30\n0.0\n")
                f.write(f"40\n{altura:.4f}\n")
                f.write(f"1\n{texto}\n")
            f.write("0\nENDSEC\n0\nEOF\n")


def exportar_autocad(app, factor, ruta):
    scale = factor
    ALTURA_TEXTO_COTA = 0.08
    ALTURA_TEXTO_TITULO = 0.22 * 0.7
    OFFSET_COTA = 0.35
    OFFSET_COTA_GENERAL_EXTRA = 0.5
    ESPACIO_VISTAS = 2.2
    TICK_SIZE = 0.06

    paneles = app._generar_paneles()
    paneles_estructura = [p for p in paneles if p["color"] != COLOR_PUERTA]
    paneles_puertas = [p for p in paneles if p["color"] == COLOR_PUERTA]

    rects_front, rects_side, rects_top = [], [], []
    for p in paneles_estructura:
        x0, y0, z0, x1, y1, z1 = p["caja"]
        rects_front.append((x0, y0, x1, y1))
        rects_side.append((z0, y0, z1, y1))
        rects_top.append((x0, z0, x1, z1))

    edges_front = _union_edges(rects_front)
    edges_side = _union_edges(rects_side)
    edges_top = _union_edges(rects_top)

    front_x, front_y = 1.0, 1.0
    side_right_x, side_right_y = front_x + app.W * scale + ESPACIO_VISTAS, front_y
    side_left_x, side_left_y = front_x - app.D * scale - ESPACIO_VISTAS, front_y
    top_x, top_y = front_x, front_y + app.H * scale + ESPACIO_VISTAS

    lienzo = _LienzoDXF(scale, ALTURA_TEXTO_COTA, ALTURA_TEXTO_TITULO,
                         OFFSET_COTA, OFFSET_COTA_GENERAL_EXTRA, TICK_SIZE)

    # --- Vista frontal ---
    for (x1c, y1c), (x2c, y2c) in edges_front:
        lienzo.lineas_mueble.append((x1c * scale + front_x, y1c * scale + front_y,
                                      x2c * scale + front_x, y2c * scale + front_y))
    for p in paneles_puertas:
        dx0, dy0, _, dx1, dy1, _ = p["caja"]
        px0, py0 = dx0 * scale + front_x, dy0 * scale + front_y
        px1, py1 = dx1 * scale + front_x, dy1 * scale + front_y
        lienzo.lineas_mueble.append((px0, py0, px1, py0))
        lienzo.lineas_mueble.append((px1, py0, px1, py1))
        lienzo.lineas_mueble.append((px1, py1, px0, py1))
        lienzo.lineas_mueble.append((px0, py1, px0, py0))
    for hx0, hy0, hx1, hy1, base in app.get_all_cells():
        if app.zoclo and base[1] == 0 and base[3] == app.zoclo["altura"]:
            continue
        tipo = app.tipos_espacio.get(app.clave_espacio(hy0, hy1, hx0, hx1), "vacio")
        if tipo != "vacio":
            continue
        cx0, cx1 = hx0 + app._inset_x(hx0), hx1 - app._inset_x(hx1)
        cy0, cy1 = hy0 + app._inset_y(hy0), hy1 - app._inset_y(hy1)
        if cx1 - cx0 <= 0.1 or cy1 - cy0 <= 0.1:
            continue
        px0, py0 = cx0 * scale + front_x, cy0 * scale + front_y
        px1, py1 = cx1 * scale + front_x, cy1 * scale + front_y
        lienzo.lineas_cotas.append((px0, py0, px1, py1))
        lienzo.lineas_cotas.append((px0, py1, px1, py0))
    lienzo.fila_cotas(app.limites_x(), lambda c: (c * scale + front_x, app.H * scale + front_y),
                       0, OFFSET_COTA)
    lienzo.fila_cotas(app.limites_y(), lambda c: (front_x, c * scale + front_y),
                       -OFFSET_COTA, 0)
    lienzo.textos_titulos.append((front_x + app.W * scale / 2, front_y - 0.35,
                                   "Front View", ALTURA_TEXTO_TITULO))

    # --- Vista lateral derecha ---
    for (z1c, y1c), (z2c, y2c) in edges_side:
        lienzo.lineas_mueble.append((z1c * scale + side_right_x, y1c * scale + side_right_y,
                                      z2c * scale + side_right_x, y2c * scale + side_right_y))
    lienzo.fila_cotas([0, app.D], lambda c: (c * scale + side_right_x, app.H * scale + side_right_y),
                       0, OFFSET_COTA)
    lienzo.fila_cotas(app.limites_y(), lambda c: (side_right_x, c * scale + side_right_y),
                       -OFFSET_COTA, 0)
    lienzo.textos_titulos.append((side_right_x + app.D * scale / 2, side_right_y - 0.35,
                                   "Right Side View", ALTURA_TEXTO_TITULO))

    # --- Vista lateral izquierda ---
    for (z1c, y1c), (z2c, y2c) in edges_side:
        lienzo.lineas_mueble.append((z1c * scale + side_left_x, y1c * scale + side_left_y,
                                      z2c * scale + side_left_x, y2c * scale + side_left_y))
    lienzo.fila_cotas([0, app.D], lambda c: (c * scale + side_left_x, app.H * scale + side_left_y),
                       0, OFFSET_COTA)
    lienzo.fila_cotas(app.limites_y(), lambda c: (side_left_x, c * scale + side_left_y),
                       -OFFSET_COTA, 0)
    lienzo.textos_titulos.append((side_left_x + app.D * scale / 2, side_left_y - 0.35,
                                   "Left Side View", ALTURA_TEXTO_TITULO))

    # --- Vista planta ---
    for (x1c, z1c), (x2c, z2c) in edges_top:
        lienzo.lineas_mueble.append((x1c * scale + top_x, z1c * scale + top_y,
                                      x2c * scale + top_x, z2c * scale + top_y))
    lienzo.fila_cotas(app.limites_x(), lambda c: (c * scale + top_x, app.D * scale + top_y),
                       0, OFFSET_COTA)
    lienzo.fila_cotas([0, app.D], lambda c: (top_x, c * scale + top_y),
                       -OFFSET_COTA, 0)
    lienzo.textos_titulos.append((top_x + app.W * scale / 2, top_y - 0.35,
                                   "Top View", ALTURA_TEXTO_TITULO))

    lienzo.escribir(ruta)


@dataclass
class Panel:
    tipo: str
    pos: float
    inicio: float
    fin: float
    fondo: float


@dataclass
class CorteLocal:
    tipo: str
    pos: float
    x0: float
    y0: float
    x1: float
    y1: float
    fondo: float = 0.0


class FurnitureDesigner:
    def __init__(self, root):
        self.root = root
        self.root.title("UA3D Modular - Cabinets")
        self.root.geometry("1500x820")

        self.W = 300
        self.H = 200
        self.D = 40
        self.espesor_marco = 1.8
        self.espesor_panel = 1.8
        self.escala = 1.3

        self.paneles_h: List[Panel] = []
        self.paneles_v: List[Panel] = []
        self._inicializar_paneles_default()

        self.perimetral = {
            "izquierdo": {"visible": True, "inicio": 0, "fin": self.H},
            "derecho":   {"visible": True, "inicio": 0, "fin": self.H},
            "inferior":  {"visible": True, "inicio": 0, "fin": self.W},
            "superior":  {"visible": True, "inicio": 0, "fin": self.W},
        }

        self.cortes_locales: List[CorteLocal] = []
        self.tipos_espacio: Dict[Tuple[float, float, float, float], str] = {}
        self.remetido_puertas: Dict[Tuple[float, float, float, float], float] = {}
        self.zoclo = None

        self.arrastrando = None
        self.indice_arrastre = -1
        self.offset = 0
        self.door_grid_cache = None
        self._dragging = False

        self.menu_activo = None

        self.mx = 75
        self.my_top = 55
        self.my_bottom = 45

        self.angulo_azimut = 35.0
        self.angulo_elev = 22.0
        self.zoom_3d = 1.0
        self.pan_x3d = 0
        self.pan_y3d = 0
        self._ultimo_x3d = 0
        self._ultimo_y3d = 0
        self._pan_ultimo_x = 0
        self._pan_ultimo_y = 0

        self.panel_dividido = None

        self.crear_widgets()
        self.dibujar_todo()

    def _inicializar_paneles_default(self):
        self.paneles_h.clear()
        self.paneles_v.clear()

        self.paneles_h.append(Panel('h', 60, 0, self.W, self.D))
        self.paneles_h.append(Panel('h', 130, 0, self.W, self.D))
        self.paneles_v.append(Panel('v', 150, 0, self.H, self.D))

    # --------------------------------------------------------
    # DETECCIÓN CENTRALIZADA
    # --------------------------------------------------------
    def _punto_en_rect(self, x, y, x0, y0, x1, y1, margen=0.0):
        return (x0 - margen) <= x <= (x1 + margen) and (y0 - margen) <= y <= (y1 + margen)

    def detectar_elemento(self, x_cm: float, y_cm: float, margen: float):
        # Perimetral izquierdo
        p = self.perimetral.get("izquierdo")
        if p and p["visible"]:
            x0, x1 = 0, self.espesor_marco
            if self._punto_en_rect(x_cm, y_cm, x0, p["inicio"], x1, p["fin"], margen):
                return ('perim_izq', None)
        # Perimetral derecho
        p = self.perimetral.get("derecho")
        if p and p["visible"]:
            x0, x1 = self.W - self.espesor_marco, self.W
            if self._punto_en_rect(x_cm, y_cm, x0, p["inicio"], x1, p["fin"], margen):
                return ('perim_der', None)
        # Perimetral inferior
        p = self.perimetral.get("inferior")
        if p and p["visible"]:
            y_inf = self.zoclo["altura"] if self.zoclo else 0
            y0, y1 = y_inf, y_inf + self.espesor_marco
            if self._punto_en_rect(x_cm, y_cm, p["inicio"], y0, p["fin"], y1, margen):
                return ('perim_inf', None)
        # Perimetral superior
        p = self.perimetral.get("superior")
        if p and p["visible"]:
            y0, y1 = self.H - self.espesor_marco, self.H
            if self._punto_en_rect(x_cm, y_cm, p["inicio"], y0, p["fin"], y1, margen):
                return ('perim_sup', None)

        # Paneles internos horizontales
        for i, p in enumerate(self.paneles_h):
            x0 = p.inicio + self._inset_x(p.inicio)
            x1 = p.fin - self._inset_x(p.fin)
            y0 = p.pos - self.espesor_panel / 2
            y1 = p.pos + self.espesor_panel / 2
            if self._punto_en_rect(x_cm, y_cm, x0, y0, x1, y1, margen):
                return ('h', i)
        # Paneles internos verticales
        for i, p in enumerate(self.paneles_v):
            y0 = p.inicio + self._inset_y(p.inicio)
            y1 = p.fin - self._inset_y(p.fin)
            x0 = p.pos - self.espesor_panel / 2
            x1 = p.pos + self.espesor_panel / 2
            if self._punto_en_rect(x_cm, y_cm, x0, y0, x1, y1, margen):
                return ('v', i)
        # Cortes locales horizontales
        for i, c in enumerate(self.cortes_locales):
            if c.tipo == 'h':
                x0 = c.x0 + self._inset_x(c.x0)
                x1 = c.x1 - self._inset_x(c.x1)
                y0 = c.pos - self.espesor_panel / 2
                y1 = c.pos + self.espesor_panel / 2
                if self._punto_en_rect(x_cm, y_cm, x0, y0, x1, y1, margen):
                    return ('h_local', i)
            else:
                y0 = c.y0 + self._inset_y(c.y0)
                y1 = c.y1 - self._inset_y(c.y1)
                x0 = c.pos - self.espesor_panel / 2
                x1 = c.pos + self.espesor_panel / 2
                if self._punto_en_rect(x_cm, y_cm, x0, y0, x1, y1, margen):
                    return ('v_local', i)
        # Celdas
        celda = self.celda_en(x_cm, y_cm)
        if celda:
            return ('celda', celda)
        return (None, None)

    # --------------------------------------------------------
    # WIDGETS
    # --------------------------------------------------------
    def crear_widgets(self):
        frame_datos = tk.Frame(self.root, bg="#eef2f5")
        frame_datos.pack(side=tk.TOP, fill=tk.X)

        # Recuadro con título: deja claro que estos 5 campos + el botón
        # de abajo son un solo grupo ("aplica estos valores"), en vez de
        # que el botón "Apply" parezca suelto sin decir a qué corresponde.
        grupo_dim = tk.LabelFrame(frame_datos, text="Cabinet Dimensions", bg="#eef2f5",
                                   font=("Arial", 8, "bold"), fg="#444", padx=4, pady=2)
        grupo_dim.pack(side=tk.LEFT, padx=(6, 10), pady=4)

        for texto, attr in [("Width (cm):", "entry_w"), ("Height (cm):", "entry_h"),
                             ("Depth (cm):", "entry_d")]:
            tk.Label(grupo_dim, text=texto, bg="#eef2f5").pack(side=tk.LEFT, padx=(8, 2), pady=4)
            e = tk.Entry(grupo_dim, width=6)
            e.pack(side=tk.LEFT)
            setattr(self, attr, e)
        self.entry_w.insert(0, str(self.W))
        self.entry_h.insert(0, str(self.H))
        self.entry_d.insert(0, str(self.D))

        tk.Label(grupo_dim, text="Frame (cm):", bg="#eef2f5").pack(side=tk.LEFT, padx=(8, 2), pady=4)
        self.entry_marco = tk.Entry(grupo_dim, width=6)
        self.entry_marco.pack(side=tk.LEFT)
        self.entry_marco.insert(0, str(self.espesor_marco))

        tk.Label(grupo_dim, text="Divider (cm):", bg="#eef2f5").pack(side=tk.LEFT, padx=(8, 2), pady=4)
        self.entry_divisor = tk.Entry(grupo_dim, width=6)
        self.entry_divisor.pack(side=tk.LEFT)
        self.entry_divisor.insert(0, str(self.espesor_panel))

        tk.Button(grupo_dim, text="Apply Dimensions", command=self.aplicar_datos,
                  bg="#cfe8cf").pack(side=tk.LEFT, padx=(10, 4), pady=4)

        # Enter en cualquiera de los 5 campos también confirma, además del
        # botón — así el usuario decide cuándo terminó de llenar los
        # campos, en vez de que se aplique a medias con cada Tab/clic.
        for entrada in (self.entry_w, self.entry_h, self.entry_d,
                        self.entry_marco, self.entry_divisor):
            entrada.bind('<Return>', lambda e: self.aplicar_datos())

        self.var_perim = {}
        for lado, texto in [("izquierdo", "Frame L"),
                            ("derecho", "Frame R"),
                            ("inferior", "Frame Bottom"),
                            ("superior", "Frame Top")]:
            var = tk.BooleanVar(value=self.perimetral[lado]["visible"])
            self.var_perim[lado] = var
            tk.Checkbutton(frame_datos, text=texto, variable=var,
                           command=lambda l=lado, v=var: self.toggle_perimetral(l, v.get()),
                           bg="#eef2f5").pack(side=tk.LEFT, padx=5)

        tk.Button(frame_datos, text="Reset", command=self.reiniciar,
                  bg="#f8d7da").pack(side=tk.LEFT, padx=8)

        frame_botones = tk.Frame(self.root)
        frame_botones.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)

        color_paneles = "#a5d6a7"
        botones = [
            ("+ Horizontal Panel", self.agregar_panel_horizontal, color_paneles),
            ("Distribute Horizontal", self.distribuir_horizontales, color_paneles),
            ("+ Vertical Panel", self.agregar_panel_vertical, color_paneles),
            ("Distribute Vertical", self.distribuir_verticales, color_paneles),
            ("Base", self.abrir_zoclo, color_paneles),
            ("Export OBJ", self.exportar_obj, "#ffe8b3"),
            ("Export STL", self.exportar_stl, "#ffe8b3"),
            ("Export AutoCAD", self.exportar_autocad, "#ffe8b3"),
            ("Save", self.guardar_proyecto, "#cce5ff"),
            ("Open", self.abrir_proyecto, "#cce5ff"),
            ("About", self.mostrar_acerca_de, "#e0e0e0"),
        ]
        for texto, cmd, color in botones:
            tk.Button(frame_botones, text=texto, command=cmd, bg=color).pack(side=tk.LEFT, padx=3)

        panel_dividido = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashwidth=6)
        panel_dividido.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.panel_dividido = panel_dividido

        frame_2d = tk.Frame(panel_dividido)
        self.canvas = tk.Canvas(frame_2d, bg="white", highlightthickness=1, highlightbackground="gray")
        xscroll = tk.Scrollbar(frame_2d, orient=tk.HORIZONTAL, command=self.canvas.xview)
        yscroll = tk.Scrollbar(frame_2d, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=xscroll.set, yscrollcommand=yscroll.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="ew")
        frame_2d.rowconfigure(0, weight=1)
        frame_2d.columnconfigure(0, weight=1)
        panel_dividido.add(frame_2d, minsize=400)

        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Motion>", self.on_mouse_move)
        self.canvas.bind("<ButtonPress-2>", self.on_pan_2d_start)
        self.canvas.bind("<B2-Motion>", self.on_pan_2d_move)
        self.canvas.bind("<MouseWheel>", self.on_zoom_2d)
        self.canvas.bind("<Button-4>", self.on_zoom_2d)
        self.canvas.bind("<Button-5>", self.on_zoom_2d)

        frame_3d = tk.Frame(panel_dividido)
        frame_top3d = tk.Frame(frame_3d)
        frame_top3d.pack(side=tk.TOP, fill=tk.X, pady=4)
        self.modo_solido_var = tk.BooleanVar(value=True)
        tk.Checkbutton(frame_top3d, text="Solid mode (uncheck = wireframe)",
                        variable=self.modo_solido_var, command=self.redibujar_3d).pack(side=tk.LEFT, padx=6)
        tk.Label(frame_top3d,
                 text="Drag = rotate | Wheel = zoom | Middle button = pan",
                 fg="black").pack(side=tk.LEFT, padx=10)

        self.canvas_3d = tk.Canvas(frame_3d, bg="white", highlightthickness=1, highlightbackground="gray")
        self.canvas_3d.pack(fill=tk.BOTH, expand=True)
        panel_dividido.add(frame_3d, minsize=400)

        self.canvas_3d.bind("<ButtonPress-1>", self.on_press_3d)
        self.canvas_3d.bind("<B1-Motion>", self.on_drag_3d)
        self.canvas_3d.bind("<MouseWheel>", self.on_zoom_3d)
        self.canvas_3d.bind("<Button-4>", self.on_zoom_3d)
        self.canvas_3d.bind("<Button-5>", self.on_zoom_3d)
        self.canvas_3d.bind("<ButtonPress-2>", self.on_pan_3d_start)
        self.canvas_3d.bind("<B2-Motion>", self.on_pan_3d_move)

        self.label_info = tk.Label(
            self.root,
            text="Left click = drag | Right click = edit line | Right click on cell = doors/dividers menu | "
                 "Wheel = zoom | Ctrl+S = Save | Ctrl+O = Open",
            font=("Arial", 9), fg="black")
        self.label_info.pack(side=tk.BOTTOM, pady=4)

        self.root.bind("<Escape>", self.cerrar_menu)
        self.root.bind("<Configure>", self.on_window_resize)
        self.root.bind("<Control-s>", lambda e: self.guardar_proyecto())
        self.root.bind("<Control-o>", lambda e: self.abrir_proyecto())

    # --------------------------------------------------------
    # CERRAR MENÚ CONTEXTUAL
    # --------------------------------------------------------
    def cerrar_menu(self, event=None):
        if self.menu_activo:
            self.menu_activo.unpost()
            self.menu_activo = None

    # --------------------------------------------------------
    # ACERCA DE
    # --------------------------------------------------------
    def mostrar_acerca_de(self):
        ventana = tk.Toplevel(self.root)
        ventana.title("About")
        ventana.resizable(False, False)
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass  # la ventana aun no era visible; sigue funcionando sin el grab modal

        texto = ("UA3D Modular - Cabinets\n"
                 "Version 1.0\n\n"
                 "This tool was developed by:\n"
                 "G. Ulises Alvarado Pérez\n"
                 "Architect & 3D Artist\n\n"
                 "Find me on social media as:\n"
                 "@ulisesalvarado3d")

        tk.Label(ventana, text=texto, font=("Segoe UI", 10), justify="center").pack(padx=30, pady=20)

        tk.Button(ventana, text="Close", command=ventana.destroy).pack(pady=(0, 15))
        ventana.bind('<Return>', lambda e: ventana.destroy())
        ventana.bind('<Escape>', lambda e: ventana.destroy())

    # --------------------------------------------------------
    # AUTO-SPLIT 50/50
    # --------------------------------------------------------
    def on_window_resize(self, event):
        if event.widget == self.root:
            self.root.after_idle(self._centrar_sash)

    def _centrar_sash(self):
        if self.panel_dividido:
            total = self.panel_dividido.winfo_width()
            if total > 0:
                self.panel_dividido.sash_place(0, total // 2, 0)

    # --------------------------------------------------------
    # PANEO Y ZOOM 2D
    # --------------------------------------------------------
    def on_pan_2d_start(self, event):
        self.canvas.scan_mark(event.x, event.y)

    def on_pan_2d_move(self, event):
        self.canvas.scan_dragto(event.x, event.y, gain=1)

    def on_zoom_2d(self, event):
        delta = event.delta if getattr(event, "delta", 0) else (120 if event.num == 4 else -120)
        factor = 1.1 if delta > 0 else (1 / 1.1)
        self.escala = max(0.05, min(100.0, self.escala * factor))
        self.dibujar_todo()

    # --------------------------------------------------------
    # PANEO 3D
    # --------------------------------------------------------
    def on_pan_3d_start(self, event):
        self._pan_ultimo_x = event.x
        self._pan_ultimo_y = event.y

    def on_pan_3d_move(self, event):
        dx = event.x - self._pan_ultimo_x
        dy = event.y - self._pan_ultimo_y
        self.pan_x3d += dx
        self.pan_y3d += dy
        self._pan_ultimo_x = event.x
        self._pan_ultimo_y = event.y
        self.redibujar_3d()

    # --------------------------------------------------------
    # PERIMETRALES
    # --------------------------------------------------------
    def toggle_perimetral(self, lado, estado):
        self.perimetral[lado]["visible"] = estado
        self.dibujar_todo()

    def editar_perimetral(self, lado):
        p = self.perimetral[lado]
        es_vertical = lado in ("izquierdo", "derecho")
        max_val = self.H if es_vertical else self.W
        etiqueta = "Start height" if es_vertical else "Start position"
        nombre_lado = {"izquierdo": "Left", "derecho": "Right",
                        "inferior": "Bottom", "superior": "Top"}[lado]

        ventana = tk.Toplevel(self.root)
        ventana.title(f"Edit {nombre_lado} Frame Panel")
        ventana.resizable(False, False)

        frame = tk.Frame(ventana)
        frame.pack(padx=15, pady=10)

        tk.Label(frame, text=f"{etiqueta} (cm):").grid(row=0, column=0, sticky="e", padx=5, pady=3)
        entry_inicio = tk.Entry(frame, width=8)
        entry_inicio.grid(row=0, column=1, pady=3)
        entry_inicio.insert(0, f"{p['inicio']:.1f}")

        tk.Label(frame, text="End (cm):").grid(row=1, column=0, sticky="e", padx=5, pady=3)
        entry_fin = tk.Entry(frame, width=8)
        entry_fin.grid(row=1, column=1, pady=3)
        entry_fin.insert(0, f"{p['fin']:.1f}")

        var_visible = tk.BooleanVar(value=p["visible"])
        tk.Checkbutton(ventana, text="Visible", variable=var_visible).pack(pady=5)

        def aplicar():
            try:
                inicio = float(entry_inicio.get())
                fin = float(entry_fin.get())
                if not (0 <= inicio < fin <= max_val):
                    raise ValueError
                if fin - inicio < max(2.0, self.espesor_marco):
                    raise ValueError
            except ValueError:
                messagebox.showerror("Error", f"Invalid values. Must satisfy 0 ≤ start < end ≤ {max_val} "
                                                f"and a minimum gap of {max(2.0, self.espesor_marco):.1f} cm.")
                return
            p["inicio"], p["fin"] = inicio, fin
            p["visible"] = var_visible.get()
            if hasattr(self, 'var_perim'):
                self.var_perim[lado].set(var_visible.get())
            ventana.destroy()
            self.dibujar_todo()

        tk.Button(ventana, text="OK", command=aplicar, bg="#cfe8cf").pack(pady=10)
        ventana.bind('<Return>', lambda e: aplicar())
        ventana.bind('<Escape>', lambda e: ventana.destroy())
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass  # la ventana aun no era visible; sigue funcionando sin el grab modal

    # --------------------------------------------------------
    # DATOS DEL MUEBLE
    # --------------------------------------------------------
    def aplicar_datos(self):
        ESPESOR_MIN = 0.3
        try:
            nuevo_w = float(self.entry_w.get())
            nuevo_h = float(self.entry_h.get())
            nuevo_d = float(self.entry_d.get())
            nuevo_marco = float(self.entry_marco.get())
            nuevo_divisor = float(self.entry_divisor.get())
            if min(nuevo_w, nuevo_h, nuevo_d, nuevo_marco, nuevo_divisor) <= 0:
                raise ValueError
            if nuevo_marco < ESPESOR_MIN or nuevo_divisor < ESPESOR_MIN:
                raise ValueError(f"Frame and Divider must be at least {ESPESOR_MIN} cm")
        except ValueError as e:
            msg = str(e) or "Values must be positive numbers (in cm)."
            messagebox.showerror("Error", msg)
            return

        fx = nuevo_w / self.W if self.W != 0 else 1
        fy = nuevo_h / self.H if self.H != 0 else 1

        # Se captura la asignación de puertas/remetido por POSICIÓN EN LA
        # REJILLA (fila/columna), no por coordenada — así no importa que
        # multiplicar y redondear coordenadas acumule un poquito de error
        # (eso fue lo que causaba que algunas puertas se "perdieran": el
        # redondeo a 1 decimal de la celda vieja, escalado, a veces cae en
        # un decimal distinto al de la celda nueva real).
        grid_tipos = self.capturar_tipos_grid()
        grid_remetido = self.capturar_remetido_grid()

        # La altura del zócalo es una medida física fija (como el espesor
        # del marco) — no crece ni se encoge solo porque cambie el alto
        # general. Pero cualquier pieza que estuviera pegada justo en esa
        # altura debe seguir pegada ahí después del cambio (si no, se abre
        # el hueco que viste en la imagen entre el panel y la Base).
        altura_zoclo_vieja = self.zoclo["altura"] if self.zoclo else 0.0
        altura_zoclo_nueva = min(altura_zoclo_vieja, max(0.0, nuevo_h - 2.0))

        for p in self.paneles_h:
            pos_orig, inicio_orig, fin_orig = p.pos, p.inicio, p.fin
            if abs(pos_orig - altura_zoclo_vieja) < 1e-6:
                p.pos = altura_zoclo_nueva
            elif abs(pos_orig - self.H) < 1e-6:
                p.pos = nuevo_h
            else:
                p.pos = pos_orig * fy
            p.inicio = 0 if abs(inicio_orig) < 1e-6 else inicio_orig * fx
            p.fin = nuevo_w if abs(fin_orig - self.W) < 1e-6 else fin_orig * fx

        for p in self.paneles_v:
            pos_orig, inicio_orig, fin_orig = p.pos, p.inicio, p.fin
            p.pos = nuevo_w if abs(pos_orig - self.W) < 1e-6 else pos_orig * fx
            p.inicio = altura_zoclo_nueva if abs(inicio_orig - altura_zoclo_vieja) < 1e-6 else inicio_orig * fy
            p.fin = nuevo_h if abs(fin_orig - self.H) < 1e-6 else fin_orig * fy

        for lado, p in self.perimetral.items():
            inicio_orig, fin_orig = p["inicio"], p["fin"]
            if lado in ("izquierdo", "derecho"):
                p["inicio"] = (altura_zoclo_nueva if abs(inicio_orig - altura_zoclo_vieja) < 1e-6
                               else inicio_orig * fy)
                p["fin"] = nuevo_h if abs(fin_orig - self.H) < 1e-6 else fin_orig * fy
            else:
                p["inicio"] = inicio_orig * fx
                p["fin"] = nuevo_w if abs(fin_orig - self.W) < 1e-6 else fin_orig * fx
            p["inicio"] = max(0, min(p["inicio"], nuevo_h if lado in ("izquierdo","derecho") else nuevo_w))
            p["fin"] = max(p["inicio"], min(p["fin"], nuevo_h if lado in ("izquierdo","derecho") else nuevo_w))

        if self.zoclo:
            self.zoclo["altura"] = altura_zoclo_nueva
            self.zoclo["remetimiento"] = min(self.zoclo["remetimiento"], max(0.0, nuevo_d - 0.5))

        # El fondo de cada panel es independiente del Depth general (para
        # permitir estantes más cortos a propósito). Pero si un panel ya
        # ocupaba el fondo COMPLETO del mueble, debe seguir ocupando el
        # fondo completo tras el cambio — si no, se queda "corto" y en la
        # vista 3D se ve como si no llegara hasta la orilla.
        for p in self.paneles_h + self.paneles_v:
            if abs(p.fondo - self.D) < 1e-6:
                p.fondo = nuevo_d
            else:
                p.fondo = min(p.fondo, nuevo_d)

        if self.cortes_locales:
            for corte in self.cortes_locales:
                corte.x0 *= fx
                corte.x1 *= fx
                corte.y0 *= fy
                corte.y1 *= fy
                corte.pos *= fx if corte.tipo == "v" else fy
                if abs(corte.fondo - self.D) < 1e-6:
                    corte.fondo = nuevo_d
                else:
                    corte.fondo = min(corte.fondo, nuevo_d)

        nuevos_remetidos_max = max(0.0, nuevo_d - nuevo_divisor - 0.1)

        self.W, self.H, self.D = nuevo_w, nuevo_h, nuevo_d
        self.espesor_marco = nuevo_marco
        self.espesor_panel = nuevo_divisor

        # Ya con W/H actualizados, limites_x()/limites_y() reflejan la
        # rejilla nueva — se reaplican por índice, con precisión exacta.
        self.aplicar_tipos_grid(grid_tipos)
        self.aplicar_remetido_grid(grid_remetido, maximo=nuevos_remetidos_max)

        for p in self.paneles_h + self.paneles_v:
            if p.fondo > self.D:
                p.fondo = self.D
        for c in self.cortes_locales:
            if c.fondo > self.D:
                c.fondo = self.D

        self.dibujar_todo()

    # --------------------------------------------------------
    # AÑADIR / DISTRIBUIR / REINICIAR
    # --------------------------------------------------------
    def _propagar_tipos_por_particion(self):
        """Cuando una celda se divide (panel nuevo o Split), las celdas
        resultantes heredan la puerta/tipo de la celda vieja que las
        contenía, comparando por el centro de cada celda nueva contra el
        rango de las celdas viejas — así una fila/columna con puerta, al
        partirse, reparte esa puerta a los pedazos en vez de perderla."""
        viejos_tipos = list(self.tipos_espacio.items())
        viejos_remetidos = dict(self.remetido_puertas)
        nuevos_tipos = {}
        nuevos_remetidos = {}
        for hx0, hy0, hx1, hy1, base in self.get_all_cells():
            cx, cy = (hx0 + hx1) / 2, (hy0 + hy1) / 2
            for (oy0, oy1, ox0, ox1), tipo in viejos_tipos:
                if ox0 - 0.05 <= cx <= ox1 + 0.05 and oy0 - 0.05 <= cy <= oy1 + 0.05:
                    clave = self.clave_espacio(hy0, hy1, hx0, hx1)
                    nuevos_tipos[clave] = tipo
                    vieja_clave = (oy0, oy1, ox0, ox1)
                    if vieja_clave in viejos_remetidos:
                        nuevos_remetidos[clave] = viejos_remetidos[vieja_clave]
                    break
        self.tipos_espacio = nuevos_tipos
        self.remetido_puertas = nuevos_remetidos

    def agregar_panel_horizontal(self):
        if not self.paneles_h:
            nueva_y = self.H / 2
        else:
            y_min = self.zoclo["altura"] if self.zoclo else 0
            puntos = [y_min] + sorted([p.pos for p in self.paneles_h]) + [self.H]
            gaps = [(puntos[i+1] - puntos[i], puntos[i] + (puntos[i+1] - puntos[i]) / 2)
                    for i in range(len(puntos)-1)]
            _, nueva_y = max(gaps, key=lambda g: g[0])
        self.paneles_h.append(Panel('h', nueva_y, 0, self.W, self.D))
        self._propagar_tipos_por_particion()
        self.dibujar_todo()

    def agregar_panel_vertical(self):
        if not self.paneles_v:
            nueva_x = self.W / 2
        else:
            puntos = [0] + sorted([p.pos for p in self.paneles_v]) + [self.W]
            gaps = [(puntos[i+1] - puntos[i], puntos[i] + (puntos[i+1] - puntos[i]) / 2)
                    for i in range(len(puntos)-1)]
            _, nueva_x = max(gaps, key=lambda g: g[0])
        inicio_y = self.zoclo["altura"] if self.zoclo else 0
        self.paneles_v.append(Panel('v', nueva_x, inicio_y, self.H, self.D))
        self._propagar_tipos_por_particion()
        self.dibujar_todo()

    def distribuir_horizontales(self):
        n = len(self.paneles_h)
        if n < 1:
            return
        grid = self.capturar_tipos_grid()
        self.paneles_h.sort(key=lambda p: p.pos)
        y_min = self.zoclo["altura"] if self.zoclo else 0
        paso = (self.H - y_min) / (n + 1)
        for i, p in enumerate(self.paneles_h):
            p.pos = y_min + paso * (i + 1)
        self.aplicar_tipos_grid(grid)
        self.dibujar_todo()

    def distribuir_verticales(self):
        n = len(self.paneles_v)
        if n < 1:
            return
        grid = self.capturar_tipos_grid()
        self.paneles_v.sort(key=lambda p: p.pos)
        paso = self.W / (n + 1)
        for i, p in enumerate(self.paneles_v):
            p.pos = paso * (i + 1)
        self.aplicar_tipos_grid(grid)
        self.dibujar_todo()

    def reiniciar(self):
        self.W = 300
        self.H = 200
        self.D = 40
        self.espesor_marco = 1.8
        self.espesor_panel = 1.8
        self.entry_w.delete(0, tk.END)
        self.entry_w.insert(0, "300")
        self.entry_h.delete(0, tk.END)
        self.entry_h.insert(0, "200")
        self.entry_d.delete(0, tk.END)
        self.entry_d.insert(0, "40")
        self.entry_marco.delete(0, tk.END)
        self.entry_marco.insert(0, "1.8")
        self.entry_divisor.delete(0, tk.END)
        self.entry_divisor.insert(0, "1.8")

        self._inicializar_paneles_default()
        self.perimetral = {
            "izquierdo": {"visible": True, "inicio": 0, "fin": self.H},
            "derecho":   {"visible": True, "inicio": 0, "fin": self.H},
            "inferior":  {"visible": True, "inicio": 0, "fin": self.W},
            "superior":  {"visible": True, "inicio": 0, "fin": self.W},
        }
        self.tipos_espacio = {}
        self.remetido_puertas = {}
        self.cortes_locales = []
        self.zoclo = None
        for lado, var in self.var_perim.items():
            var.set(True)
        self.dibujar_todo()

    # --------------------------------------------------------
    # CAPTURAR / APLICAR PATRÓN DE PUERTAS
    # --------------------------------------------------------
    def capturar_tipos_grid(self):
        lx = self.limites_x()
        ly = self.limites_y()
        grid = []
        for i in range(len(ly)-1):
            fila = []
            for j in range(len(lx)-1):
                clave = self.clave_espacio(ly[i], ly[i+1], lx[j], lx[j+1])
                fila.append(self.tipos_espacio.get(clave, "vacio"))
            grid.append(fila)
        return grid

    def aplicar_tipos_grid(self, grid):
        self.tipos_espacio = {}
        lx = self.limites_x()
        ly = self.limites_y()
        for i in range(len(ly)-1):
            for j in range(len(lx)-1):
                tipo = grid[i][j] if i < len(grid) and j < len(grid[i]) else "vacio"
                if tipo != "vacio":
                    clave = self.clave_espacio(ly[i], ly[i+1], lx[j], lx[j+1])
                    self.tipos_espacio[clave] = tipo

    def capturar_remetido_grid(self):
        lx = self.limites_x()
        ly = self.limites_y()
        grid = []
        for i in range(len(ly)-1):
            fila = []
            for j in range(len(lx)-1):
                clave = self.clave_espacio(ly[i], ly[i+1], lx[j], lx[j+1])
                fila.append(self.remetido_puertas.get(clave, 0.0))
            grid.append(fila)
        return grid

    def aplicar_remetido_grid(self, grid, maximo=None):
        self.remetido_puertas = {}
        lx = self.limites_x()
        ly = self.limites_y()
        for i in range(len(ly)-1):
            for j in range(len(lx)-1):
                valor = grid[i][j] if i < len(grid) and j < len(grid[i]) else 0.0
                if valor > 1e-6:
                    if maximo is not None:
                        valor = min(valor, maximo)
                    clave = self.clave_espacio(ly[i], ly[i+1], lx[j], lx[j+1])
                    self.remetido_puertas[clave] = valor

    # --------------------------------------------------------
    # ZOCLO
    # --------------------------------------------------------
    def abrir_zoclo(self):
        ventana = tk.Toplevel(self.root)
        ventana.title("Base")
        ventana.resizable(False, False)

        tk.Label(ventana, text="Base Settings", font=("Arial", 11, "bold")).pack(pady=(10, 6))
        frame_campos = tk.Frame(ventana)
        frame_campos.pack(padx=15, pady=5)

        tk.Label(frame_campos, text="Height (cm):").grid(row=0, column=0, sticky="e", padx=5, pady=3)
        entry_altura = tk.Entry(frame_campos, width=8)
        entry_altura.grid(row=0, column=1, pady=3)

        tk.Label(frame_campos, text="Setback (cm):").grid(row=1, column=0, sticky="e", padx=5, pady=3)
        entry_rem = tk.Entry(frame_campos, width=8)
        entry_rem.grid(row=1, column=1, pady=3)

        if self.zoclo:
            entry_altura.insert(0, f"{self.zoclo['altura']:.1f}")
            entry_rem.insert(0, f"{self.zoclo['remetimiento']:.1f}")
        else:
            entry_altura.insert(0, "10")
            entry_rem.insert(0, "5")

        def agregar_o_actualizar():
            try:
                altura = float(entry_altura.get())
                rem = float(entry_rem.get())
                if altura <= 0 or rem < 0 or rem >= self.D:
                    raise ValueError
            except ValueError:
                messagebox.showerror("Error", "Height > 0 and setback between 0 and depth.")
                return

            paneles_h_backup = [(p.pos, p.inicio, p.fin, p.fondo) for p in self.paneles_h]
            paneles_v_backup = [(p.pos, p.inicio, p.fin, p.fondo) for p in self.paneles_v]
            perim_backup = {k: v.copy() for k, v in self.perimetral.items()}
            zoclo_backup = self.zoclo.copy() if self.zoclo else None

            altura_vieja = self.zoclo["altura"] if self.zoclo else 0.0

            for p in self.paneles_h:
                if abs(p.pos - altura_vieja) < 1e-6:
                    p.pos = altura
            for p in self.paneles_v:
                if abs(p.inicio - altura_vieja) < 1e-6:
                    p.inicio = altura

            self.perimetral["izquierdo"]["inicio"] = altura
            self.perimetral["derecho"]["inicio"] = altura

            conflictos = [p for p in self.paneles_h if p.pos < altura]
            if conflictos:
                for p, (pos, inicio, fin, fondo) in zip(self.paneles_h, paneles_h_backup):
                    p.pos, p.inicio, p.fin, p.fondo = pos, inicio, fin, fondo
                for p, (pos, inicio, fin, fondo) in zip(self.paneles_v, paneles_v_backup):
                    p.pos, p.inicio, p.fin, p.fondo = pos, inicio, fin, fondo
                self.perimetral = perim_backup
                self.zoclo = zoclo_backup
                messagebox.showerror("Conflict", "There are horizontal panels below the toe kick height.")
                return

            self.zoclo = {"altura": altura, "remetimiento": rem}
            self._remigrar_tipos_por_zoclo(altura_vieja, altura)
            self._reajustar_cortes_locales('h', altura_vieja, altura)
            ventana.destroy()
            self.dibujar_todo()

        def quitar():
            if self.zoclo:
                altura_vieja = self.zoclo["altura"]
                for p in self.paneles_h:
                    if abs(p.pos - altura_vieja) < 1e-6:
                        p.pos = 0
                for p in self.paneles_v:
                    if abs(p.inicio - altura_vieja) < 1e-6:
                        p.inicio = 0
                self.perimetral["izquierdo"]["inicio"] = 0
                self.perimetral["derecho"]["inicio"] = 0
                self.zoclo = None
                self._remigrar_tipos_por_zoclo(altura_vieja, 0.0)
                self._reajustar_cortes_locales('h', altura_vieja, 0.0)
                ventana.destroy()
                self.dibujar_todo()
            else:
                messagebox.showinfo("Base", "No base to remove.")

        tk.Button(ventana, text="Add / Update", command=agregar_o_actualizar,
                  bg="#cfe8cf").pack(pady=5, padx=15, fill="x")
        tk.Button(ventana, text="Remove", command=quitar,
                  bg="#f8d7da").pack(pady=5, padx=15, fill="x")
        ventana.bind('<Return>', lambda e: agregar_o_actualizar())
        ventana.bind('<Escape>', lambda e: ventana.destroy())
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass  # la ventana aun no era visible; sigue funcionando sin el grab modal

    # --------------------------------------------------------
    # CONVERSIONES DE COORDENADAS
    # --------------------------------------------------------
    def cm_a_px(self, x, y):
        px = x * self.escala + self.mx
        py = (self.H - y) * self.escala + self.my_top
        return px, py

    def px_a_cm(self, px, py):
        x = (px - self.mx) / self.escala
        y = self.H - (py - self.my_top) / self.escala
        return x, y

    # --------------------------------------------------------
    # GRILLA DE ESPACIOS
    # --------------------------------------------------------
    def limites_x(self):
        return [0] + sorted([p.pos for p in self.paneles_v]) + [self.W]

    def limites_y(self):
        puntos = [0]
        if self.zoclo:
            puntos.append(self.zoclo["altura"])
        puntos.extend([p.pos for p in self.paneles_h])
        puntos.append(self.H)
        return sorted(set(puntos))

    def clave_espacio(self, y0, y1, x0, x1):
        return (round(y0, 1), round(y1, 1), round(x0, 1), round(x1, 1))

    def celdas_base(self):
        lx, ly = self.limites_x(), self.limites_y()
        celdas = []
        for i in range(len(ly)-1):
            for j in range(len(lx)-1):
                celdas.append((ly[i], ly[i+1], lx[j], lx[j+1]))
        return celdas

    @staticmethod
    def _rect_igual(a, b):
        return all(abs(a[k] - b[k]) < 1e-3 for k in range(4))

    def hojas_de_celda(self, celda_base):
        x0b, y0b, x1b, y1b = celda_base
        rects = [(x0b, y0b, x1b, y1b)]
        for corte in self.cortes_locales:
            objetivo = (corte.x0, corte.y0, corte.x1, corte.y1)
            for i, r in enumerate(rects):
                if self._rect_igual(r, objetivo):
                    rx0, ry0, rx1, ry1 = r
                    if corte.tipo == "h":
                        nueva1 = (rx0, ry0, rx1, corte.pos)
                        nueva2 = (rx0, corte.pos, rx1, ry1)
                    else:
                        nueva1 = (rx0, ry0, corte.pos, ry1)
                        nueva2 = (corte.pos, ry0, rx1, ry1)
                    rects[i:i+1] = [nueva1, nueva2]
                    break
        return rects

    def get_all_cells(self):
        hojas = []
        for (y0, y1, x0, x1) in self.celdas_base():
            base = (x0, y0, x1, y1)
            for hoja in self.hojas_de_celda(base):
                hx0, hy0, hx1, hy1 = hoja
                hojas.append((hx0, hy0, hx1, hy1, base))
        return hojas

    def celda_en(self, x_cm, y_cm):
        if not (0 <= x_cm <= self.W and 0 <= y_cm <= self.H):
            return None
        for hx0, hy0, hx1, hy1, base in self.get_all_cells():
            if hx0 - 1e-6 <= x_cm <= hx1 + 1e-6 and hy0 - 1e-6 <= y_cm <= hy1 + 1e-6:
                return (hy0, hy1, hx0, hx1, base)
        return None

    # --------------------------------------------------------
    # DIBUJO 2D (rectángulos)
    # --------------------------------------------------------
    def dibujar_rect_panel(self, x0, y0, x1, y1, fill, outline, width=1, dash=None):
        px0, py0 = self.cm_a_px(x0, y1)
        px1, py1 = self.cm_a_px(x1, y0)
        self.canvas.create_rectangle(px0, py0, px1, py1,
                                     fill=fill, outline=outline,
                                     width=width, dash=dash)

    def dibujar_panel_h(self, panel: Panel):
        xa = panel.inicio + self._inset_x(panel.inicio)
        xb = panel.fin - self._inset_x(panel.fin)
        y0 = panel.pos - self.espesor_panel / 2
        y1 = panel.pos + self.espesor_panel / 2
        self.dibujar_rect_panel(xa, y0, xb, y1,
                                fill="#90caf9", outline="#1565c0", width=1)

    def dibujar_panel_v(self, panel: Panel):
        ya = panel.inicio + self._inset_y(panel.inicio)
        yb = panel.fin - self._inset_y(panel.fin)
        x0 = panel.pos - self.espesor_panel / 2
        x1 = panel.pos + self.espesor_panel / 2
        self.dibujar_rect_panel(x0, ya, x1, yb,
                                fill="#f48fb1", outline="#ad1457", width=1)

    def dibujar_corte_local(self, corte: CorteLocal):
        if corte.tipo == "h":
            xa = corte.x0 + self._inset_x(corte.x0)
            xb = corte.x1 - self._inset_x(corte.x1)
            y0 = corte.pos - self.espesor_panel / 2
            y1 = corte.pos + self.espesor_panel / 2
            self.dibujar_rect_panel(xa, y0, xb, y1,
                                    fill="#90caf9", outline="#1565c0",
                                    width=1, dash=(3,2))
        else:
            ya = corte.y0 + self._inset_y(corte.y0)
            yb = corte.y1 - self._inset_y(corte.y1)
            x0 = corte.pos - self.espesor_panel / 2
            x1 = corte.pos + self.espesor_panel / 2
            self.dibujar_rect_panel(x0, ya, x1, yb,
                                    fill="#f48fb1", outline="#ad1457",
                                    width=1, dash=(3,2))

    def dibujar_perimetral(self, lado, visible):
        p = self.perimetral[lado]
        e = self.espesor_marco
        if lado == "izquierdo":
            x0, x1 = 0, e
            y0, y1 = p["inicio"], p["fin"]
        elif lado == "derecho":
            x0, x1 = self.W - e, self.W
            y0, y1 = p["inicio"], p["fin"]
        elif lado == "inferior":
            y_inf = self.zoclo["altura"] if self.zoclo else 0
            x0, x1 = p["inicio"], p["fin"]
            y0, y1 = y_inf, y_inf + e
        elif lado == "superior":
            x0, x1 = p["inicio"], p["fin"]
            y0, y1 = self.H - e, self.H

        if visible:
            self.dibujar_rect_panel(x0, y0, x1, y1,
                                    fill="#d8d8d8", outline="#777777", width=1)
        else:
            self.dibujar_rect_panel(x0, y0, x1, y1,
                                    fill="", outline="#aaaaaa", width=1, dash=(4,4))

    def dibujar_puerta(self, x0px, y0px, x1px, y1px, doble):
        ancho = abs(x1px - x0px)
        alto = abs(y1px - y0px)
        # reveal/gap se ajustan al tamaño disponible en pantalla para que
        # nunca inviertan el rectángulo (lo que hacía desaparecer la puerta
        # doble cuando el mueble es muy grande y hay que alejar el zoom).
        reveal = max(1.0, min(4.0, ancho * 0.08, alto * 0.08))
        if not doble:
            self.canvas.create_rectangle(x0px+reveal, y0px+reveal, x1px-reveal, y1px-reveal,
                                          fill="#ffe0b3", outline="#e67e22", width=2)
            hx = x1px - reveal - min(8.0, ancho * 0.15)
            hy = (y0px + y1px) / 2
            self.canvas.create_oval(hx-3, hy-3, hx+3, hy+3, fill="#7a4a00", outline="")
        else:
            mid = (x0px + x1px) / 2
            medio_ancho = ancho / 2
            gap = max(0.5, min(2.0, (medio_ancho - reveal) * 0.3))
            if medio_ancho - reveal <= 0:
                # Celda demasiado angosta incluso para el reveal mínimo:
                # se dibuja igual como una sola hoja, para que no desaparezca.
                self.canvas.create_rectangle(x0px+reveal, y0px+reveal, x1px-reveal, y1px-reveal,
                                              fill="#ffe0b3", outline="#e67e22", width=2)
                return
            self.canvas.create_rectangle(x0px+reveal, y0px+reveal, mid-gap, y1px-reveal,
                                          fill="#ffe0b3", outline="#e67e22", width=2)
            self.canvas.create_rectangle(mid+gap, y0px+reveal, x1px-reveal, y1px-reveal,
                                          fill="#ffe0b3", outline="#e67e22", width=2)
            hy = (y0px + y1px) / 2
            self.canvas.create_oval(mid-gap-6, hy-3, mid-gap, hy+3, fill="#7a4a00", outline="")
            self.canvas.create_oval(mid+gap, hy-3, mid+gap+6, hy+3, fill="#7a4a00", outline="")

    def dibujar_cotas_h(self):
        puntos = self.limites_y()
        for i in range(len(puntos)-1):
            y1c, y2c = puntos[i], puntos[i+1]
            dist = y2c - y1c
            if dist < 1:
                continue
            px1, py1 = self.cm_a_px(0, y1c)
            px2, py2 = self.cm_a_px(0, y2c)
            x_cota = px1 - 25
            self.canvas.create_line(px1, py1, px1-15, py1, fill="gray", dash=(2, 2))
            self.canvas.create_line(px2, py2, px1-15, py2, fill="gray", dash=(2, 2))
            self.canvas.create_line(x_cota, py1, x_cota, py2, fill="gray", width=1)
            self.canvas.create_line(x_cota-3, py1-4, x_cota, py1, arrow=tk.LAST, fill="gray")
            self.canvas.create_line(x_cota-3, py2+4, x_cota, py2, arrow=tk.FIRST, fill="gray")
            self.canvas.create_text(x_cota-20, (py1+py2)/2, text=f"{dist:.1f} cm",
                                     font=("Arial", 9, "bold"), fill="#333")

    def dibujar_cotas_v(self):
        puntos = self.limites_x()
        for i in range(len(puntos)-1):
            x1c, x2c = puntos[i], puntos[i+1]
            dist = x2c - x1c
            if dist < 1:
                continue
            px1, py1 = self.cm_a_px(x1c, self.H)
            px2, py2 = self.cm_a_px(x2c, self.H)
            y_cota = py1 - 25
            self.canvas.create_line(px1, py1, px1, py1-15, fill="gray", dash=(2, 2))
            self.canvas.create_line(px2, py2, px2, py2-15, fill="gray", dash=(2, 2))
            self.canvas.create_line(px1, y_cota, px2, y_cota, fill="gray", width=1)
            self.canvas.create_line(px1+4, y_cota-3, px1, y_cota, arrow=tk.FIRST, fill="gray")
            self.canvas.create_line(px2-4, y_cota-3, px2, y_cota, arrow=tk.LAST, fill="gray")
            self.canvas.create_text((px1+px2)/2, y_cota-15, text=f"{dist:.1f} cm",
                                     font=("Arial", 9, "bold"), fill="#333")

    def dibujar_todo(self):
        self.canvas.delete("all")

        x0, y0 = self.cm_a_px(0, 0)
        x1, y1 = self.cm_a_px(self.W, self.H)
        self.canvas.create_rectangle(x0, y0, x1, y1, outline="#cccccc", width=1, dash=(4, 4))

        self.canvas.create_oval(x0-4, y0-4, x0+4, y0+4, fill="red", outline="")
        self.canvas.create_text(x0-8, y0+14, text="(0,0)", fill="red",
                                 font=("Arial", 8, "bold"), anchor="e")
        self.canvas.create_line(x0, y0, x0+20, y0, fill="red", arrow=tk.LAST)
        self.canvas.create_line(x0, y0, x0, y0-20, fill="red", arrow=tk.LAST)

        if self.zoclo:
            hz = self.zoclo["altura"]
            px0, py_bottom = self.cm_a_px(0, 0)
            px1, py_top = self.cm_a_px(self.W, hz)
            self.canvas.create_rectangle(px0, py_top, px1, py_bottom,
                                         fill="#f0f0f0", outline="#999", stipple="gray25")
            self.canvas.create_text((px0+px1)/2, (py_top+py_bottom)/2,
                                    text="Base", fill="#555", font=("Arial", 9, "bold"))

        for hx0, hy0, hx1, hy1, base in self.get_all_cells():
            bx0, by0, bx1, by1 = base
            if self.zoclo and by0 == 0 and by1 == self.zoclo["altura"]:
                continue
            tipo = self.tipos_espacio.get(self.clave_espacio(hy0, hy1, hx0, hx1), "vacio")
            if tipo != "vacio":
                pxA, pyA = self.cm_a_px(hx0, hy1)
                pxB, pyB = self.cm_a_px(hx1, hy0)
                self.dibujar_puerta(pxA, pyA, pxB, pyB, doble=(tipo == "puerta_doble"))

        for panel in self.paneles_h:
            self.dibujar_panel_h(panel)

        for panel in self.paneles_v:
            self.dibujar_panel_v(panel)

        for corte in self.cortes_locales:
            self.dibujar_corte_local(corte)

        for lado in ["izquierdo", "derecho", "inferior", "superior"]:
            self.dibujar_perimetral(lado, self.perimetral[lado]["visible"])

        self.dibujar_cotas_h()
        self.dibujar_cotas_v()

        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

        if not self._dragging:
            self.redibujar_3d()

    # --------------------------------------------------------
    # EVENTOS DE RATÓN 2D
    # --------------------------------------------------------
    def on_mouse_move(self, event):
        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        x_cm, y_cm = self.px_a_cm(cx, cy)
        margen = 4 / self.escala
        tipo, _ = self.detectar_elemento(x_cm, y_cm, margen)

        if tipo in ('h', 'h_local'):
            self.canvas.config(cursor="sb_v_double_arrow")
        elif tipo in ('v', 'v_local'):
            self.canvas.config(cursor="sb_h_double_arrow")
        elif tipo is not None and tipo.startswith('perim_'):
            self.canvas.config(cursor="hand2")
        else:
            self.canvas.config(cursor="")

    def on_click(self, event):
        if self.menu_activo:
            self.cerrar_menu()
            return

        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        x_cm, y_cm = self.px_a_cm(cx, cy)
        margen = 4 / self.escala
        tipo, dato = self.detectar_elemento(x_cm, y_cm, margen)

        if tipo in ('h', 'v', 'h_local', 'v_local'):
            self.arrastrando = tipo
            self.indice_arrastre = dato
            if tipo == 'h':
                self.offset = y_cm - self.paneles_h[dato].pos
            elif tipo == 'v':
                self.offset = x_cm - self.paneles_v[dato].pos
            elif tipo == 'h_local':
                self.offset = y_cm - self.cortes_locales[dato].pos
            elif tipo == 'v_local':
                self.offset = x_cm - self.cortes_locales[dato].pos

            self.door_grid_cache = self.capturar_tipos_grid() if tipo in ('h', 'v') else None
            self._dragging = True

    def on_right_click(self, event):
        self.cerrar_menu()

        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        x_cm, y_cm = self.px_a_cm(cx, cy)
        margen = 4 / self.escala
        tipo, dato = self.detectar_elemento(x_cm, y_cm, margen)

        if tipo.startswith('perim_'):
            mapa_lados = {'izq': 'izquierdo', 'der': 'derecho',
                          'inf': 'inferior', 'sup': 'superior'}
            lado = mapa_lados[tipo.replace('perim_', '')]
            self.editar_perimetral(lado)
        elif tipo == 'h':
            panel = self.paneles_h[dato]
            self.editar_panel("h", dato, panel.pos, panel.inicio, panel.fin, panel.fondo, self.H, "Height")
        elif tipo == 'v':
            panel = self.paneles_v[dato]
            self.editar_panel("v", dato, panel.pos, panel.inicio, panel.fin, panel.fondo, self.W, "Distance")
        elif tipo in ('h_local', 'v_local'):
            self.editar_corte_local(dato)
        elif tipo == 'celda':
            y0, y1, x0, x1, base = dato
            if self.zoclo and base[1] == 0 and base[3] == self.zoclo["altura"]:
                return
            self.menu_celda(event, x0, y0, x1, y1)

    def menu_celda(self, event, x0, y0, x1, y1):
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label="Split Horizontal", command=lambda: self.dividir_celda_directa("h", x0, y0, x1, y1))
        menu.add_command(label="Split Vertical", command=lambda: self.dividir_celda_directa("v", x0, y0, x1, y1))
        menu.add_separator()
        menu.add_command(label="Single Door", command=lambda: self.asignar_puerta_directa("puerta_simple", x0, y0, x1, y1))
        menu.add_command(label="Double Door", command=lambda: self.asignar_puerta_directa("puerta_doble", x0, y0, x1, y1))
        menu.add_command(label="Remove Door / Empty", command=lambda: self.asignar_puerta_directa("vacio", x0, y0, x1, y1))
        tipo_actual = self.tipos_espacio.get(self.clave_espacio(y0, y1, x0, x1), "vacio")
        if tipo_actual != "vacio":
            menu.add_separator()
            menu.add_command(label="Recess Panel...", command=lambda: self.editar_remetido_puerta(x0, y0, x1, y1))
        self.menu_activo = menu
        menu.tk_popup(event.x_root, event.y_root)
        self.menu_activo = None

    def dividir_celda_directa(self, tipo, x0, y0, x1, y1):
        pos = (y0 + y1) / 2 if tipo == "h" else (x0 + x1) / 2
        self.cortes_locales.append(CorteLocal(tipo=tipo, pos=pos,
                                              x0=x0, y0=y0, x1=x1, y1=y1, fondo=self.D))
        self._propagar_tipos_por_particion()
        self.dibujar_todo()

    def asignar_puerta_directa(self, tipo, x0, y0, x1, y1):
        clave = self.clave_espacio(y0, y1, x0, x1)
        if tipo == "vacio":
            self.tipos_espacio.pop(clave, None)
            self.remetido_puertas.pop(clave, None)
        else:
            self.tipos_espacio[clave] = tipo
        self.dibujar_todo()

    def editar_remetido_puerta(self, x0, y0, x1, y1):
        clave = self.clave_espacio(y0, y1, x0, x1)
        actual = self.remetido_puertas.get(clave, 0.0)

        ventana = tk.Toplevel(self.root)
        ventana.title("Recess Panel")
        ventana.resizable(False, False)

        tk.Label(ventana, text="Recess distance from the front edge (cm):").pack(padx=15, pady=(15, 5))
        entry = tk.Entry(ventana, width=8)
        entry.pack(pady=5)
        entry.insert(0, f"{actual:.1f}")
        entry.focus_set()
        entry.select_range(0, tk.END)

        def aplicar():
            try:
                valor = float(entry.get())
                maximo = self.D - self.espesor_panel - 0.1
                if not (0 <= valor <= maximo):
                    raise ValueError(f"Must be between 0 and {maximo:.1f} cm")
            except ValueError as e:
                messagebox.showerror("Error", f"Invalid value: {e}")
                return
            if valor <= 1e-6:
                self.remetido_puertas.pop(clave, None)
            else:
                self.remetido_puertas[clave] = valor
            ventana.destroy()
            self.redibujar_3d()

        tk.Button(ventana, text="OK", command=aplicar, bg="#cfe8cf").pack(pady=10)
        ventana.bind('<Return>', lambda e: aplicar())
        ventana.bind('<Escape>', lambda e: ventana.destroy())
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass

    def eliminar_panel(self, tipo, indice):
        if tipo == "h":
            del self.paneles_h[indice]
        else:
            del self.paneles_v[indice]
        self.dibujar_todo()

    def on_motion(self, event):
        if self.arrastrando is None:
            return
        cx = self.canvas.canvasx(event.x)
        cy = self.canvas.canvasy(event.y)
        x_cm, y_cm = self.px_a_cm(cx, cy)
        tolerancia_snap = 4 / self.escala
        MIN_HUECO = max(2.0, self.espesor_marco, self.espesor_panel)   # frente al marco/zoclo
        MIN_HUECO_PANEL = max(2.0, self.espesor_panel)                  # entre 2 paneles internos

        if self.arrastrando == 'h':
            idx = self.indice_arrastre
            panel = self.paneles_h[idx]
            ys = sorted([p.pos for p in self.paneles_h])
            y_min = self.zoclo["altura"] if self.zoclo else 0
            lower, upper = y_min, self.H
            margen_lower = MIN_HUECO   # zoclo / marco inferior: sin cambios
            margen_upper = self.espesor_marco if self.perimetral["superior"]["visible"] else 0.0
            sorted_idx = ys.index(panel.pos)
            if sorted_idx > 0:
                lower = ys[sorted_idx - 1]
                margen_lower = MIN_HUECO_PANEL
            if sorted_idx < len(ys) - 1:
                upper = ys[sorted_idx + 1]
                margen_upper = MIN_HUECO_PANEL

            if lower < y_min:
                lower = y_min

            nuevo_y = self._clamp_asimetrico(y_cm - self.offset, lower, upper, margen_lower, margen_upper)
            if lower == y_min and nuevo_y < y_min + MIN_HUECO:
                nuevo_y = y_min

            viejo_y = panel.pos
            panel.pos = nuevo_y
            self._reajustar_cortes_locales('h', viejo_y, nuevo_y)
            if self.door_grid_cache:
                self.aplicar_tipos_grid(self.door_grid_cache)
            self.dibujar_todo()
        elif self.arrastrando == 'v':
            idx = self.indice_arrastre
            panel = self.paneles_v[idx]
            xs = sorted([p.pos for p in self.paneles_v])
            lower, upper = 0, self.W
            margen_lower = self.espesor_marco if self.perimetral["izquierdo"]["visible"] else 0.0
            margen_upper = self.espesor_marco if self.perimetral["derecho"]["visible"] else 0.0
            sorted_idx = xs.index(panel.pos)
            if sorted_idx > 0:
                lower = xs[sorted_idx - 1]
                margen_lower = MIN_HUECO_PANEL
            if sorted_idx < len(xs) - 1:
                upper = xs[sorted_idx + 1]
                margen_upper = MIN_HUECO_PANEL

            nuevo_x = self._clamp_asimetrico(x_cm - self.offset, lower, upper, margen_lower, margen_upper)

            viejo_x = panel.pos
            panel.pos = nuevo_x
            self._reajustar_cortes_locales('v', viejo_x, nuevo_x)
            if self.door_grid_cache:
                self.aplicar_tipos_grid(self.door_grid_cache)
            self.dibujar_todo()
        elif self.arrastrando == 'h_local':
            idx = self.indice_arrastre
            corte = self.cortes_locales[idx]
            objetivo = max(corte.y0, min(corte.y1, y_cm - self.offset))
            candidatos = [p.pos for p in self.paneles_h] + [
                c.pos for j, c in enumerate(self.cortes_locales)
                if j != idx and c.tipo == "h"
            ]
            objetivo = self._snap(objetivo, candidatos, tolerancia_snap)
            viejo_pos = corte.pos
            corte.pos = self._clamp_seguro(objetivo, corte.y0, corte.y1, MIN_HUECO)
            self._reajustar_cortes_locales('h', viejo_pos, corte.pos)
            self.dibujar_todo()
        elif self.arrastrando == 'v_local':
            idx = self.indice_arrastre
            corte = self.cortes_locales[idx]
            objetivo = max(corte.x0, min(corte.x1, x_cm - self.offset))
            candidatos = [p.pos for p in self.paneles_v] + [
                c.pos for j, c in enumerate(self.cortes_locales)
                if j != idx and c.tipo == "v"
            ]
            objetivo = self._snap(objetivo, candidatos, tolerancia_snap)
            viejo_pos = corte.pos
            corte.pos = self._clamp_seguro(objetivo, corte.x0, corte.x1, MIN_HUECO)
            self._reajustar_cortes_locales('v', viejo_pos, corte.pos)
            self.dibujar_todo()

    def on_release(self, event):
        self.arrastrando = None
        self.indice_arrastre = -1
        self.door_grid_cache = None
        if self._dragging:
            self._dragging = False
            self.redibujar_3d()

    # --------------------------------------------------------
    # UTILIDADES PARA ARRASTRE
    # --------------------------------------------------------
    def _snap(self, valor, candidatos, tolerancia):
        mejor = None
        for c in candidatos:
            d = abs(c - valor)
            if d < tolerancia and (mejor is None or d < abs(mejor - valor)):
                mejor = c
        return mejor if mejor is not None else valor

    def _reajustar_cortes_locales(self, eje, valor_viejo, valor_nuevo):
        if abs(valor_viejo - valor_nuevo) < 1e-6:
            return
        tol = 0.05
        campos = ("y0", "y1") if eje == "h" else ("x0", "x1")
        for corte in self.cortes_locales:
            for campo in campos:
                if abs(getattr(corte, campo) - valor_viejo) < tol:
                    setattr(corte, campo, valor_nuevo)
            if corte.tipo == eje:
                lo = corte.y0 if eje == "h" else corte.x0
                hi = corte.y1 if eje == "h" else corte.x1
                corte.pos = max(lo, min(hi, corte.pos))

    def _remigrar_tipos_por_zoclo(self, altura_vieja, altura_nueva):
        if abs(altura_vieja - altura_nueva) < 1e-6:
            return
        nuevos = {}
        for (y0, y1, x0, x1), tipo in self.tipos_espacio.items():
            if abs(y0 - altura_vieja) < 0.15:
                nuevos[self.clave_espacio(altura_nueva, y1, x0, x1)] = tipo
            else:
                nuevos[(y0, y1, x0, x1)] = tipo
        self.tipos_espacio = nuevos

    def _clamp_seguro(self, valor, lower, upper, margen):
        rango = upper - lower
        if rango <= 2 * margen:
            return (lower + upper) / 2
        return max(lower + margen, min(upper - margen, valor))

    def _clamp_asimetrico(self, valor, lower, upper, margen_lower, margen_upper):
        """Como _clamp_seguro, pero con un margen distinto en cada lado —
        se usa para permitir llegar al 0/W/H exacto cuando ese marco
        perimetral está apagado, sin aflojar la separación mínima
        real entre paneles internos."""
        rango = upper - lower
        if rango <= margen_lower + margen_upper:
            return (lower + upper) / 2
        return max(lower + margen_lower, min(upper - margen_upper, valor))

    # --------------------------------------------------------
    # ELIMINAR CORTE Y DEPENDIENTES
    # --------------------------------------------------------
    def eliminar_corte_y_dependientes(self, indice):
        corte = self.cortes_locales[indice]
        rx0, ry0, rx1, ry1 = corte.x0, corte.y0, corte.x1, corte.y1
        if corte.tipo == "h":
            hijos = [(rx0, ry0, rx1, corte.pos), (rx0, corte.pos, rx1, ry1)]
        else:
            hijos = [(rx0, ry0, corte.pos, ry1), (corte.pos, ry0, rx1, ry1)]
        a_borrar = {indice}
        cambio = True
        while cambio:
            cambio = False
            for j, c in enumerate(self.cortes_locales):
                if j in a_borrar:
                    continue
                rect_c = (c.x0, c.y0, c.x1, c.y1)
                if any(self._rect_igual(rect_c, h) for h in hijos):
                    a_borrar.add(j)
                    if c.tipo == "h":
                        hijos.append((c.x0, c.y0, c.x1, c.pos))
                        hijos.append((c.x0, c.pos, c.x1, c.y1))
                    else:
                        hijos.append((c.x0, c.y0, c.pos, c.y1))
                        hijos.append((c.pos, c.y0, c.x1, c.y1))
                    cambio = True
        self.cortes_locales = [c for j, c in enumerate(self.cortes_locales) if j not in a_borrar]

    # --------------------------------------------------------
    # EDITAR PANEL Y CORTE LOCAL
    # --------------------------------------------------------
    def editar_panel(self, tipo, indice, pos_actual, inicio_actual, fin_actual, fondo_actual, max_val, etiqueta):
        ventana = tk.Toplevel(self.root)
        ventana.title("Edit Panel")
        ventana.resizable(False, False)

        es_horizontal = (tipo == 'h')
        if es_horizontal:
            texto_pos = "Height (cm):"
            texto_inicio = "Start X (cm):"
            texto_fin = "End X (cm):"
            max_perp = self.W
        else:
            texto_pos = "Distance (cm):"
            texto_inicio = "Start Y (cm):"
            texto_fin = "End Y (cm):"
            max_perp = self.H

        tk.Label(ventana, text=f"{etiqueta}: {pos_actual:.1f} cm",
                 font=("Arial", 10, "bold")).pack(padx=15, pady=(12, 6))

        frame = tk.Frame(ventana)
        frame.pack(padx=15, pady=5, fill="x")

        tk.Label(frame, text=texto_pos).grid(row=0, column=0, sticky="e", pady=2)
        entry_pos = tk.Entry(frame, width=8)
        entry_pos.grid(row=0, column=1)
        entry_pos.insert(0, f"{pos_actual:.1f}")

        tk.Label(frame, text=texto_inicio).grid(row=1, column=0, sticky="e", pady=2)
        entry_inicio = tk.Entry(frame, width=8)
        entry_inicio.grid(row=1, column=1)
        entry_inicio.insert(0, f"{inicio_actual:.1f}")

        tk.Label(frame, text=texto_fin).grid(row=2, column=0, sticky="e", pady=2)
        entry_fin = tk.Entry(frame, width=8)
        entry_fin.grid(row=2, column=1)
        entry_fin.insert(0, f"{fin_actual:.1f}")

        tk.Label(frame, text="Depth (cm):").grid(row=3, column=0, sticky="e", pady=2)
        entry_fondo = tk.Entry(frame, width=8)
        entry_fondo.grid(row=3, column=1)
        entry_fondo.insert(0, f"{fondo_actual:.1f}")

        def aplicar():
            try:
                nuevo_pos = float(entry_pos.get())
                nuevo_inicio = float(entry_inicio.get())
                nuevo_fin = float(entry_fin.get())
                nuevo_fondo = float(entry_fondo.get())

                if not (0 <= nuevo_pos <= max_val):
                    raise ValueError(f"Position out of range (0 - {max_val:.1f})")
                if not (0 <= nuevo_inicio < nuevo_fin <= max_perp):
                    raise ValueError(f"Invalid Start/End (0 ≤ start < end ≤ {max_perp:.1f})")
                if nuevo_fin - nuevo_inicio < max(2.0, self.espesor_panel):
                    raise ValueError(f"Minimum length {max(2.0, self.espesor_panel):.1f} cm")
                if not (0 < nuevo_fondo <= self.D):
                    raise ValueError("Depth must be between 0 and the overall depth")

                otras = self.paneles_h if es_horizontal else self.paneles_v
                MIN_HUECO = max(2.0, self.espesor_panel)
                for j, p in enumerate(otras):
                    if j != indice and abs(p.pos - nuevo_pos) < MIN_HUECO:
                        raise ValueError("Too close to another panel: leave at least "
                                         f"{MIN_HUECO:.1f} cm of gap")
            except ValueError as e:
                messagebox.showerror("Error", f"Invalid value: {e}")
                return

            panel = (self.paneles_h if es_horizontal else self.paneles_v)[indice]
            viejo_pos = panel.pos
            panel.pos = nuevo_pos
            panel.inicio = nuevo_inicio
            panel.fin = nuevo_fin
            panel.fondo = nuevo_fondo
            self._reajustar_cortes_locales('h' if es_horizontal else 'v', viejo_pos, nuevo_pos)
            ventana.destroy()
            self.dibujar_todo()

        def eliminar():
            self.eliminar_panel(tipo, indice)
            ventana.destroy()

        btn_frame = tk.Frame(ventana)
        btn_frame.pack(pady=10)
        tk.Button(btn_frame, text="OK", command=aplicar, bg="#cfe8cf", width=10).pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="Delete Panel", command=eliminar, bg="#f8d7da", width=12).pack(side=tk.LEFT, padx=5)
        ventana.bind('<Return>', lambda e: aplicar())
        ventana.bind('<Escape>', lambda e: ventana.destroy())
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass  # la ventana aun no era visible; sigue funcionando sin el grab modal

    def editar_corte_local(self, indice):
        corte = self.cortes_locales[indice]
        etiqueta = "Height from floor" if corte.tipo == "h" else "Distance from left"
        minimo = corte.y0 if corte.tipo == "h" else corte.x0
        maximo = corte.y1 if corte.tipo == "h" else corte.x1

        ventana = tk.Toplevel(self.root)
        ventana.title("Edit Divider")
        ventana.resizable(False, False)
        tk.Label(ventana, text=f"{etiqueta}: {corte.pos:.1f} cm",
                 font=("Arial", 10, "bold")).pack(padx=15, pady=(12, 6))

        frame_pos = tk.Frame(ventana)
        frame_pos.pack(padx=15, pady=5, fill="x")
        tk.Label(frame_pos, text=f"New value ({minimo:.1f} - {maximo:.1f}):").pack(side=tk.LEFT)
        entry_pos = tk.Entry(frame_pos, width=8)
        entry_pos.pack(side=tk.LEFT, padx=5)
        entry_pos.insert(0, f"{corte.pos:.1f}")

        frame_fondo = tk.Frame(ventana)
        frame_fondo.pack(padx=15, pady=5, fill="x")
        tk.Label(frame_fondo, text="New depth (cm, max D):").pack(side=tk.LEFT)
        entry_fondo = tk.Entry(frame_fondo, width=8)
        entry_fondo.pack(side=tk.LEFT, padx=5)
        entry_fondo.insert(0, f"{corte.fondo:.1f}")

        def aplicar():
            try:
                nuevo_pos = float(entry_pos.get())
                nuevo_fondo = float(entry_fondo.get())
                MIN_HUECO = max(2.0, self.espesor_panel)
                if not (minimo + MIN_HUECO <= nuevo_pos <= maximo - MIN_HUECO):
                    raise ValueError(f"Must stay at least {MIN_HUECO:.1f} cm from both edges of the cell")
                if not (0 < nuevo_fondo <= self.D):
                    raise ValueError("Depth must be between 0 and the overall depth")
            except ValueError as e:
                messagebox.showerror("Error", f"Invalid value: {e}")
                return
            viejo_pos = corte.pos
            corte.pos = nuevo_pos
            corte.fondo = nuevo_fondo
            self._reajustar_cortes_locales(corte.tipo, viejo_pos, nuevo_pos)
            ventana.destroy()
            self.dibujar_todo()

        def eliminar():
            self.eliminar_corte_y_dependientes(indice)
            ventana.destroy()
            self.dibujar_todo()

        btn_frame = tk.Frame(ventana)
        btn_frame.pack(pady=10)
        tk.Button(btn_frame, text="OK", command=aplicar, bg="#cfe8cf", width=10).pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="Delete Divider", command=eliminar, bg="#f8d7da", width=14).pack(side=tk.LEFT, padx=5)
        ventana.bind('<Return>', lambda e: aplicar())
        ventana.bind('<Escape>', lambda e: ventana.destroy())
        ventana.transient(self.root)
        ventana.update_idletasks()
        try:
            ventana.grab_set()
        except tk.TclError:
            pass  # la ventana aun no era visible; sigue funcionando sin el grab modal

    # --------------------------------------------------------
    # GEOMETRÍA COMPARTIDA (vista 3D y exportación)
    # --------------------------------------------------------
    def _inset_x(self, x):
        if (abs(x - 0) < 1e-6 and self.perimetral.get("izquierdo", {}).get("visible", False)) or \
           (abs(x - self.W) < 1e-6 and self.perimetral.get("derecho", {}).get("visible", False)):
            return self.espesor_marco
        return 0.0

    def _inset_y(self, y):
        if abs(y - self.H) < 1e-6 and self.perimetral.get("superior", {}).get("visible", False):
            return self.espesor_marco
        if self.zoclo:
            if abs(y - self.zoclo["altura"]) < 1e-6 and self.perimetral.get("inferior", {}).get("visible", False):
                return self.espesor_marco
        else:
            if abs(y) < 1e-6 and self.perimetral.get("inferior", {}).get("visible", False):
                return self.espesor_marco
        return 0.0

    def _generar_paneles(self):
        paneles = []
        e_marco = self.espesor_marco
        e_panel = self.espesor_panel
        half_marco = e_marco / 2
        half_panel = e_panel / 2

        if self.zoclo:
            y_base = self.zoclo["altura"]
            rem = self.zoclo["remetimiento"]
            paneles.append({"caja": (0, 0, 0, self.W, y_base, self.D - rem),
                            "color": "#8b5a2b"})
        else:
            y_base = 0

        if self.perimetral["izquierdo"]["visible"]:
            p = self.perimetral["izquierdo"]
            paneles.append({"caja": (0, p["inicio"], 0, e_marco, p["fin"], self.D),
                            "color": "#d8d8d8"})
        if self.perimetral["derecho"]["visible"]:
            p = self.perimetral["derecho"]
            paneles.append({"caja": (self.W - e_marco, p["inicio"], 0, self.W, p["fin"], self.D),
                            "color": "#d8d8d8"})
        if self.perimetral["inferior"]["visible"]:
            p = self.perimetral["inferior"]
            y0_inf = self.zoclo["altura"] if self.zoclo else 0
            paneles.append({"caja": (p["inicio"], y0_inf, 0, p["fin"], y0_inf + e_marco, self.D),
                            "color": "#d8d8d8"})
        if self.perimetral["superior"]["visible"]:
            p = self.perimetral["superior"]
            paneles.append({"caja": (p["inicio"], self.H - e_marco, 0, p["fin"], self.H, self.D),
                            "color": "#d8d8d8"})

        for panel in self.paneles_v:
            ya = panel.inicio + self._inset_y(panel.inicio)
            yb = panel.fin - self._inset_y(panel.fin)
            if yb - ya > 0.01:
                paneles.append({"caja": (panel.pos - half_panel, ya, 0,
                                         panel.pos + half_panel, yb, panel.fondo),
                                "color": "#f48fb1"})

        for panel in self.paneles_h:
            xa = panel.inicio + self._inset_x(panel.inicio)
            xb = panel.fin - self._inset_x(panel.fin)
            if xb - xa > 0.01:
                paneles.append({"caja": (xa, panel.pos - half_panel, 0,
                                         xb, panel.pos + half_panel, panel.fondo),
                                "color": "#90caf9"})

        for corte in self.cortes_locales:
            if corte.tipo == "h":
                xa = corte.x0 + self._inset_x(corte.x0)
                xb = corte.x1 - self._inset_x(corte.x1)
                if xb - xa > 0.01:
                    paneles.append({"caja": (xa, corte.pos - half_panel, 0,
                                             xb, corte.pos + half_panel, corte.fondo),
                                    "color": "#90caf9"})
            else:
                ya = corte.y0 + self._inset_y(corte.y0)
                yb = corte.y1 - self._inset_y(corte.y1)
                if yb - ya > 0.01:
                    paneles.append({"caja": (corte.pos - half_panel, ya, 0,
                                             corte.pos + half_panel, yb, corte.fondo),
                                    "color": "#f48fb1"})

        for x0, y0, x1, y1, base in self.get_all_cells():
            if self.zoclo and base[1] == 0 and base[3] == self.zoclo["altura"]:
                continue
            clave = self.clave_espacio(y0, y1, x0, x1)
            tipo = self.tipos_espacio.get(clave, "vacio")
            if tipo == "vacio":
                continue

            cx0 = x0 + self._inset_x(x0)
            cx1 = x1 - self._inset_x(x1)
            cy0 = y0 + self._inset_y(y0)
            cy1 = y1 - self._inset_y(y1)

            if cx1 - cx0 <= 0.1 or cy1 - cy0 <= 0.1:
                continue

            z_atras = self.D - e_panel - self.remetido_puertas.get(clave, 0.0)
            z_delante = z_atras + e_panel
            color_puerta = "#d9a066"

            if tipo == "puerta_simple":
                paneles.append({"caja": (cx0, cy0, z_atras, cx1, cy1, z_delante),
                                "color": color_puerta})
            elif tipo == "puerta_doble":
                gap = 0.4
                medio = (cx0 + cx1) / 2
                if medio - gap/2 - cx0 > 0.1:
                    paneles.append({"caja": (cx0, cy0, z_atras, medio - gap/2, cy1, z_delante),
                                    "color": color_puerta})
                if cx1 - (medio + gap/2) > 0.1:
                    paneles.append({"caja": (medio + gap/2, cy0, z_atras, cx1, cy1, z_delante),
                                    "color": color_puerta})

        return paneles

    def _caras_caja(self, x0, y0, z0, x1, y1, z1):
        return [
            ([(x0, y0, z0), (x0, y1, z0), (x1, y1, z0), (x1, y0, z0)], (0, 0, -1)),
            ([(x0, y0, z1), (x1, y0, z1), (x1, y1, z1), (x0, y1, z1)], (0, 0, 1)),
            ([(x0, y0, z0), (x1, y0, z0), (x1, y0, z1), (x0, y0, z1)], (0, -1, 0)),
            ([(x1, y1, z0), (x0, y1, z0), (x0, y1, z1), (x1, y1, z1)], (0, 1, 0)),
            ([(x0, y1, z0), (x0, y0, z0), (x0, y0, z1), (x0, y1, z1)], (-1, 0, 0)),
            ([(x1, y0, z0), (x1, y1, z0), (x1, y1, z1), (x1, y0, z1)], (1, 0, 0)),
        ]

    # --------------------------------------------------------
    # VISTA 3D
    # --------------------------------------------------------
    def _proyectar_3d(self, x, y, z):
        cx, cy, cz = self.W / 2, self.H / 2, self.D / 2
        px, py, pz = x - cx, y - cy, z - cz
        a = math.radians(self.angulo_azimut)
        x1 = px * math.cos(a) - pz * math.sin(a)
        z1 = px * math.sin(a) + pz * math.cos(a)
        b = math.radians(self.angulo_elev)
        y2 = py * math.cos(b) - z1 * math.sin(b)
        z2 = py * math.sin(b) + z1 * math.cos(b)

        diag = math.sqrt(self.W ** 2 + self.H ** 2 + self.D ** 2) / 2
        distancia_camara = diag * 2.4
        profundidad_cam = max(distancia_camara - z2, distancia_camara * 0.05)
        factor = distancia_camara / profundidad_cam
        x1, y2 = x1 * factor, y2 * factor

        ancho_canvas = self.canvas_3d.winfo_width() or 650
        alto_canvas = self.canvas_3d.winfo_height() or 600
        s = 1.0 * self.zoom_3d
        return ancho_canvas / 2 + x1 * s + self.pan_x3d, alto_canvas / 2 - y2 * s + 20 + self.pan_y3d, z2

    @staticmethod
    def _sombrear(hexcolor, factor):
        hexcolor = hexcolor.lstrip("#")
        r, g, b = int(hexcolor[0:2], 16), int(hexcolor[2:4], 16), int(hexcolor[4:6], 16)
        r, g, b = (min(255, max(0, int(c * factor))) for c in (r, g, b))
        return f"#{r:02x}{g:02x}{b:02x}"

    def redibujar_3d(self):
        self.canvas_3d.delete("all")
        paneles = self._generar_paneles()
        luz = (0.4, 0.7, 0.6)
        norma = math.sqrt(sum(c * c for c in luz))
        luz = tuple(c / norma for c in luz)
        modo_solido = self.modo_solido_var.get()

        # Ambos modos comparten el mismo cálculo de caras ordenadas de atrás
        # hacia adelante (pintor's algorithm): en sólido se rellenan con
        # sombreado, en alámbrico se rellenan de blanco y solo se ve el
        # contorno — como las caras de enfrente se pintan despues, tapan
        # las líneas de lo que está detrás, así solo quedan visibles los
        # bordes de la silueta real (sin la maraña de un wireframe normal).
        caras = []
        for p in paneles:
            x0, y0, z0, x1, y1, z1 = p["caja"]
            for verts, normal in self._caras_caja(x0, y0, z0, x1, y1, z1):
                proyectados = [self._proyectar_3d(*v) for v in verts]
                profundidad = min(pv[2] for pv in proyectados)
                pts = [c for pv in proyectados for c in (pv[0], pv[1])]
                if modo_solido:
                    brillo = 0.4 + 0.6 * max(0.0, normal[0]*luz[0] + normal[1]*luz[1] + normal[2]*luz[2])
                    color = self._sombrear(p["color"], brillo)
                    caras.append((profundidad, pts, color, self._sombrear(color, 0.7)))
                else:
                    caras.append((profundidad, pts, "white", "black"))
        caras.sort(key=lambda c: c[0])
        for _, pts, color, contorno in caras:
            self.canvas_3d.create_polygon(pts, fill=color, outline=contorno, width=1)

        self.canvas_3d.create_text(
            10, 10, anchor="nw",
            text=f"Width: {self.W:.1f} cm | Height: {self.H:.1f} cm | Depth: {self.D:.1f} cm",
            font=("Arial", 10, "bold"), fill="#333")

    def on_press_3d(self, event):
        self._ultimo_x3d, self._ultimo_y3d = event.x, event.y

    def on_drag_3d(self, event):
        dx = event.x - self._ultimo_x3d
        dy = event.y - self._ultimo_y3d
        self.angulo_azimut = (self.angulo_azimut + dx * 0.4) % 360
        self.angulo_elev = max(-85, min(85, self.angulo_elev - dy * 0.4))
        self._ultimo_x3d, self._ultimo_y3d = event.x, event.y
        self.redibujar_3d()

    def on_zoom_3d(self, event):
        delta = event.delta if getattr(event, "delta", 0) else (120 if event.num == 4 else -120)
        factor = 1.1 if delta > 0 else (1 / 1.1)
        self.zoom_3d = max(0.2, min(6.0, self.zoom_3d * factor))
        self.redibujar_3d()

    # --------------------------------------------------------
    # GUARDAR / ABRIR PROYECTO
    # --------------------------------------------------------
    def guardar_proyecto(self):
        ruta = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("Cabinet Project", "*.json")],
            initialfile="cabinet.json"
        )
        if not ruta:
            return

        tipos_str = {}
        for (y0, y1, x0, x1), tipo in self.tipos_espacio.items():
            clave = f"{y0},{y1},{x0},{x1}"
            tipos_str[clave] = tipo

        remetidos_str = {}
        for (y0, y1, x0, x1), valor in self.remetido_puertas.items():
            clave = f"{y0},{y1},{x0},{x1}"
            remetidos_str[clave] = valor

        datos = {
            "W": self.W,
            "H": self.H,
            "D": self.D,
            "espesor_marco": self.espesor_marco,
            "espesor_panel": self.espesor_panel,
            "paneles_h": [{"pos": p.pos, "inicio": p.inicio, "fin": p.fin, "fondo": p.fondo} for p in self.paneles_h],
            "paneles_v": [{"pos": p.pos, "inicio": p.inicio, "fin": p.fin, "fondo": p.fondo} for p in self.paneles_v],
            "perimetral": self.perimetral,
            "zoclo": self.zoclo,
            "tipos_espacio": tipos_str,
            "remetido_puertas": remetidos_str,
            "cortes_locales": [
                {"tipo": c.tipo, "pos": c.pos, "x0": c.x0, "y0": c.y0,
                 "x1": c.x1, "y1": c.y1, "fondo": c.fondo}
                for c in self.cortes_locales
            ]
        }

        try:
            with open(ruta, "w", encoding="utf-8") as f:
                json.dump(datos, f, indent=2)
            messagebox.showinfo("Saved", f"Project saved to:\n{ruta}")
        except Exception as e:
            messagebox.showerror("Error", f"Could not save:\n{e}")

    def abrir_proyecto(self):
        ruta = filedialog.askopenfilename(
            filetypes=[("Cabinet Project", "*.json"), ("All files", "*.*")]
        )
        if not ruta:
            return

        try:
            with open(ruta, "r", encoding="utf-8") as f:
                datos = json.load(f)

            for campo in ["W", "H", "D", "espesor_marco", "espesor_panel"]:
                if campo not in datos or not isinstance(datos[campo], (int, float)) or datos[campo] <= 0:
                    raise ValueError(f"Invalid field '{campo}'.")

            self.W = float(datos["W"])
            self.H = float(datos["H"])
            self.D = float(datos["D"])
            self.espesor_marco = float(datos["espesor_marco"])
            self.espesor_panel = float(datos["espesor_panel"])

            self.paneles_h = []
            for pd in datos.get("paneles_h", []):
                self.paneles_h.append(Panel(
                    'h',
                    float(pd["pos"]),
                    float(pd.get("inicio", 0)),
                    float(pd.get("fin", self.W)),
                    float(pd.get("fondo", self.D))
                ))

            self.paneles_v = []
            for pd in datos.get("paneles_v", []):
                self.paneles_v.append(Panel(
                    'v',
                    float(pd["pos"]),
                    float(pd.get("inicio", 0)),
                    float(pd.get("fin", self.H)),
                    float(pd.get("fondo", self.D))
                ))

            per_data = datos.get("perimetral", {})
            for lado in ["izquierdo", "derecho", "inferior", "superior"]:
                if lado in per_data:
                    p = per_data[lado]
                    self.perimetral[lado] = {
                        "visible": bool(p.get("visible", True)),
                        "inicio": float(p.get("inicio", 0)),
                        "fin": float(p.get("fin", self.H if lado in ("izquierdo", "derecho") else self.W))
                    }
                else:
                    self.perimetral[lado] = {
                        "visible": True,
                        "inicio": 0,
                        "fin": self.H if lado in ("izquierdo", "derecho") else self.W
                    }

            zoclo = datos.get("zoclo", None)
            if zoclo is not None:
                if not isinstance(zoclo, dict) or "altura" not in zoclo or "remetimiento" not in zoclo:
                    raise ValueError("Invalid toe kick data.")
                self.zoclo = {"altura": float(zoclo["altura"]), "remetimiento": float(zoclo["remetimiento"])}
            else:
                self.zoclo = None

            self.tipos_espacio = {}
            for clave_str, tipo in datos.get("tipos_espacio", {}).items():
                partes = clave_str.split(",")
                if len(partes) == 4:
                    y0, y1, x0, x1 = map(float, partes)
                    self.tipos_espacio[self.clave_espacio(y0, y1, x0, x1)] = tipo

            self.remetido_puertas = {}
            for clave_str, valor in datos.get("remetido_puertas", {}).items():
                partes = clave_str.split(",")
                if len(partes) == 4:
                    y0, y1, x0, x1 = map(float, partes)
                    self.remetido_puertas[self.clave_espacio(y0, y1, x0, x1)] = float(valor)

            self.cortes_locales = []
            for cd in datos.get("cortes_locales", []):
                if cd.get("tipo") not in ("h", "v"):
                    continue
                self.cortes_locales.append(CorteLocal(
                    tipo=cd["tipo"],
                    pos=float(cd["pos"]),
                    x0=float(cd["x0"]), y0=float(cd["y0"]),
                    x1=float(cd["x1"]), y1=float(cd["y1"]),
                    fondo=float(cd.get("fondo", self.D)),
                ))

            self.entry_w.delete(0, tk.END)
            self.entry_w.insert(0, f"{self.W:.1f}")
            self.entry_h.delete(0, tk.END)
            self.entry_h.insert(0, f"{self.H:.1f}")
            self.entry_d.delete(0, tk.END)
            self.entry_d.insert(0, f"{self.D:.1f}")
            self.entry_marco.delete(0, tk.END)
            self.entry_marco.insert(0, f"{self.espesor_marco:.2f}")
            self.entry_divisor.delete(0, tk.END)
            self.entry_divisor.insert(0, f"{self.espesor_panel:.2f}")

            for lado, var in self.var_perim.items():
                var.set(self.perimetral[lado]["visible"])

            self.dibujar_todo()
            messagebox.showinfo("Opened", f"Project loaded from:\n{ruta}")
        except Exception as e:
            messagebox.showerror("Error", f"Could not open the file:\n{e}")

    # --------------------------------------------------------
    # EXPORTAR
    # --------------------------------------------------------
    def _pedir_factor_escala(self):
        return simpledialog.askfloat(
            "Scale Factor",
            "Enter scale factor (0.01 = meters, 1 = centimeters):",
            initialvalue=0.01,
            minvalue=0.0001,
            maxvalue=1000
        )

    def _exportar(self, funcion, defaultextension, filetypes, initialfile, etiqueta, nota=""):
        factor = self._pedir_factor_escala()
        if factor is None:
            return
        ruta = filedialog.asksaveasfilename(defaultextension=defaultextension,
                                             filetypes=filetypes,
                                             initialfile=initialfile)
        if not ruta:
            return
        try:
            funcion(self, factor, ruta)
        except Exception as e:
            messagebox.showerror("Error", f"Could not export:\n{e}")
            return
        messagebox.showinfo("Exported", f"{etiqueta} saved to:\n{ruta}{nota}")

    def exportar_obj(self):
        self._exportar(exportar_obj, ".obj", [("Wavefront OBJ", "*.obj")],
                        "cabinet.obj", "Model",
                        "\n\nImport in Blender: File > Import > Wavefront (.obj)")

    def exportar_stl(self):
        self._exportar(exportar_stl, ".stl", [("STL", "*.stl")],
                        "cabinet.stl", "Model",
                        "\n\nImport in Blender: File > Import > STL")

    def exportar_autocad(self):
        self._exportar(exportar_autocad, ".dxf", [("AutoCAD DXF", "*.dxf")],
                        "cabinet_elevations.dxf", "DXF")


if __name__ == "__main__":
    root = tk.Tk()
    app = FurnitureDesigner(root)
    root.mainloop()