from collections import deque
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import networkx as nx
from networkx.drawing.nx_pydot import graphviz_layout
from tkinter.simpledialog import askstring
import matplotlib.pyplot as plt
import sympy as sp

class Graph:
    def __init__(self):
        self.graph = nx.Graph()
        self.edge_count = 0
        self.edge_labels = {}
        self.undo_stack = []
        self.redo_stack = []

    def add_node(self, node_name):
        if node_name not in self.graph.nodes:
            self.graph.add_node(node_name)
            
    def remove_node(self, node_name):
        print("Before removing node:")
        print("Nodes:", self.graph.nodes)
        print("Edges:", self.graph.edges)
    
        if node_name in self.graph.nodes:
            self.graph.remove_node(node_name)
            self.edge_labels = {edge: label for edge, label in self.edge_labels.items() if node_name not in edge}

        print("After removing node:")
        print("Nodes:", self.graph.nodes)
        print("Edges:", self.graph.edges)    

    def add_edge(self, node1, node2):
        self.edge_count += 1
        edge_name = str(self.edge_count)
        if (node1, node2) not in self.graph.edges and (node2, node1) not in self.graph.edges:
            self.graph.add_edge(node1, node2)
            self.edge_labels[(node1, node2)] = edge_name

    def remove_edge(self, edge_name):
        edge_to_remove = None
        for edge, label in self.edge_labels.items():
            if label == edge_name:
                edge_to_remove = edge
                break
        if edge_to_remove:
            del self.edge_labels[edge_to_remove]
            self.graph.remove_edge(*edge_to_remove)

    def minimum_spanning_tree(self):
        try:
            mst = nx.minimum_spanning_tree(self.graph)
            
            # Check if the resulting tree spans all vertices
            if set(mst.nodes) != set(self.graph.nodes):
                return None, "Minimum spanning tree does not span all vertices."

            # Check if the resulting tree has n-1 edges
            if len(mst.edges) != len(self.graph.nodes) - 1:
                return None, "Minimum spanning tree has incorrect number of edges."
            
            # Check if the graph contains cycles
            if nx.cycle_basis(self.graph):
                return None, "Graph contains cycles and is not a tree."

            return mst, None
        except nx.NetworkXError as e:
            return None, str(e)

    def generate_tree(self, level, degree):
        self.generated_tree = nx.balanced_tree(degree, level)
        self.graph = nx.relabel_nodes(self.generated_tree, lambda x: str(x), copy=True)

        self.edge_labels.clear()
        for u, v in self.graph.edges:
            self.edge_count += 1
            edge_name = str(self.edge_count)
            self.edge_labels[(u, v)] = edge_name

    def is_tree(self):
        num_nodes = len(self.graph.nodes)
        num_edges = len(self.graph.edges)
        
        if num_edges != num_nodes - 1:
            return False

        if not nx.is_connected(self.graph):
            return False

        if nx.cycle_basis(self.graph):
            return False

        return True
    
    def is_full_binary_tree(self):
        if not self.is_tree():
            return False

        def check_full(node, parent=None):
            children = list(self.graph.neighbors(node))
            if parent is not None:
                children.remove(parent)
            if len(children) == 0:
                return True
            elif len(children) == 2:
                return check_full(children[0], node) and check_full(children[1], node)
            return False

        root = next(iter(self.graph.nodes))  # Usa el primer nodo como raíz
        return check_full(root)

    def is_complete_tree(self):
        if not self.is_tree():
            return False

        num_nodes = len(self.graph.nodes)
        max_index = max(int(node) for node in self.graph.nodes)
        expected_index = 1  # El índice esperado para el siguiente nodo hoja
        for index in range(1, max_index + 1):
            if str(index) not in self.graph.nodes:
                # Si falta un nodo, verifica si todos los nodos restantes están en el nivel más bajo
                return all(str(i) not in self.graph.nodes for i in range(index, max_index + 1))
            elif int(self.graph.degree[str(index)]) == 0:  # Si el nodo es una hoja
                if int(index) != expected_index:
                    return False
                expected_index += 1  # Actualiza el índice esperado para el próximo nodo hoja
        return True


    def is_balanced(self):
        if not self.is_tree():
            return False

        def check_balance(node, parent=None):
            children = list(self.graph.neighbors(node))
            if parent is not None:
                children.remove(parent)
            if len(children) == 0:
                return True, 0
            elif len(children) == 2:
                left_balanced, left_height = check_balance(children[0], node)
                right_balanced, right_height = check_balance(children[1], node)
                balanced = left_balanced and right_balanced and abs(left_height - right_height) <= 1
                return balanced, max(left_height, right_height) + 1
            return False, 0

        root = next(iter(self.graph.nodes))  # Usa el primer nodo como raíz
        balanced, _ = check_balance(root)
        return balanced

    def is_perfectly_balanced(self):
        if not self.is_tree():
            return False

        def check_perfect(node, parent=None):
            children = list(self.graph.neighbors(node))
            if parent is not None:
                children.remove(parent)
            if len(children) == 0:
                return True, 0
            elif len(children) == 2:
                left_perfect, left_height = check_perfect(children[0], node)
                right_perfect, right_height = check_perfect(children[1], node)
                perfect = left_perfect and right_perfect and left_height == right_height
                return perfect, left_height + 1
            return False, 0

        root = next(iter(self.graph.nodes))  # Usa el primer nodo como raíz
        perfectly_balanced, _ = check_perfect(root)
        return perfectly_balanced

    def is_avl(self):
        return self.is_balanced()
    
    def bfs_camino(self, inicio, fin):
        if inicio not in self.graph.nodes or fin not in self.graph.nodes:
            return None

        cola = deque([inicio])
        padres = {inicio: None}
        visitados = set([inicio])

        while cola:
            nodo_actual = cola.popleft()

            if nodo_actual == fin:
                break

            for vecino in self.graph.neighbors(nodo_actual):
                if vecino not in visitados:
                    visitados.add(vecino)
                    padres[vecino] = nodo_actual
                    cola.append(vecino)

        camino = []
        paso = fin
        while paso is not None:
            camino.append(paso)
            paso = padres[paso]

        camino.reverse()

        for nodo in camino:
            print(f'Coloreando nodo {nodo} de rojo')
            self.set_node_color(nodo, 'red')
        return camino

    def set_node_color(self, node, color):
        current_color = self.graph.nodes[node].get('color', 'skyblue')
        self.undo_stack.append((node, current_color))
        self.graph.nodes[node]['color'] = color

    def undo(self):
        if self.undo_stack:
            node, color = self.undo_stack.pop()
            current_color = self.graph.nodes[node].get('color', 'skyblue')
            self.redo_stack.append((node, current_color))
            self.graph.nodes[node]['color'] = color
            print("Undo realizado")

    def redo(self):
        if self.redo_stack:
            node, color = self.redo_stack.pop()
            current_color = self.graph.nodes[node].get('color', 'skyblue')
            self.undo_stack.append((node, current_color))
            self.graph.nodes[node]['color'] = color
            print("Redo realizado")

    def _clean_input(self, infix_input):
        cleaned_input = []
        for char in infix_input:
            if char.isdigit() or char in ['+', '-', '*', '/', '^', '(', ')']:
                cleaned_input.append(char)
        return cleaned_input
    

    def infix_to_postfix(self, infix_input: list) -> list:
        precedence_order = {'+': 1, '-': 1, '*': 2, '/': 2, '^': 3}
        associativity = {'+': "LR", '-': "LR", '*': "LR", '/': "LR", '^': "RL"}
        clean_infix = self._clean_input(infix_input)
        postfix = []
        operators = set(precedence_order.keys())
        stack = deque()
        
        for char in clean_infix:
            if char.isnumeric():  # Si el token es un operando
                postfix.append(char)
            elif char == '(':  # Si el token es un paréntesis de apertura
                stack.appendleft(char)
            elif char == ')':  # Si el token es un paréntesis de cierre
                while stack and stack[0] != '(':
                    postfix.append(stack.popleft())
                stack.popleft()  # Descartar el '('
            elif char in operators:  # Si el token es un operador
                while (stack and stack[0] != '(' and 
                       (precedence_order[char] < precedence_order[stack[0]] or
                        (precedence_order[char] == precedence_order[stack[0]] and associativity[char] == "LR"))):
                    postfix.append(stack.popleft())
                stack.appendleft(char)
        
        # Añadir cualquier operador restante en la pila a la salida
        while stack:
            postfix.append(stack.popleft())
        
        return postfix
    
    def build_expression_tree(self, postfix_expression):
            stack = []

            # Crear un nuevo grafo dirigido para representar el árbol de expresión
            expression_tree = nx.DiGraph()

            for token in postfix_expression:
                # Si el token es un operador
                if token in ['+', '-', '*', '/', '^']:
                    # Pop los dos últimos operandos del stack
                    operand2 = stack.pop()
                    operand1 = stack.pop()
                    # Agregar el operador como un nodo al grafo
                    expression_tree.add_node(token)
                    # Conectar el operador con sus operandos en el grafo
                    expression_tree.add_edge(token, operand1)
                    expression_tree.add_edge(token, operand2)
                    # Agregar el resultado al stack
                    stack.append(token)
                else:
                    # Si el token es un operando, agregarlo como un nodo al grafo
                    expression_tree.add_node(token)
                    # Agregar el operando al stack
                    stack.append(token)

            # Obtener el último nodo del stack, que será el nodo raíz del árbol de expresión
            root_node = stack.pop()

            return expression_tree, root_node

class GraphGUI:
    def __init__(self, root, graph):
        self.graph = graph
        self.root = root
        self.root.title("Visualizador de Grafos")
        
        # Panel izquierdo con funcionalidades
        self.left_panel = tk.Frame(self.root)
        self.left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)

        self.right_panel = tk.Frame(self.root)
        self.right_panel.pack(side=tk.RIGHT, fill=tk.Y, padx=10, pady=10)

        tk.Label(self.left_panel, text="Nombre del nodo:").pack()
        self.node_entry = tk.Entry(self.left_panel)
        self.node_entry.pack()

        add_node_button = tk.Button(self.left_panel, text="Añadir Nodo", command=self.add_node)
        add_node_button.pack()

        tk.Label(self.left_panel, text="Nodo 1:").pack()
        self.node1_entry = tk.Entry(self.left_panel)
        self.node1_entry.pack()

        tk.Label(self.left_panel, text="Nodo 2:").pack()
        self.node2_entry = tk.Entry(self.left_panel)
        self.node2_entry.pack()

        tk.Label(self.left_panel, text="Nombre de la arista:").pack()
        self.edge_entry = tk.Entry(self.left_panel)
        self.edge_entry.pack()

        add_edge_button = tk.Button(self.left_panel, text="Añadir Arista", command=self.add_edge)
        add_edge_button.pack()

        tk.Label(self.left_panel, text="Nombre del nodo a eliminar:").pack()
        self.node_remove_entry = tk.Entry(self.left_panel)
        self.node_remove_entry.pack()

        remove_node_button = tk.Button(self.left_panel, text="Eliminar Nodo", command=self.remove_node)
        remove_node_button.pack()

        tk.Label(self.left_panel, text="Nombre de la arista a eliminar:").pack()
        self.edge_remove_entry = tk.Entry(self.left_panel)
        self.edge_remove_entry.pack()

        remove_edge_button = tk.Button(self.left_panel, text="Eliminar Arista", command=self.remove_edge)
        remove_edge_button.pack()

        tk.Label(self.left_panel, text="Nivel del árbol:").pack()
        self.tree_level_entry = tk.Entry(self.left_panel)
        self.tree_level_entry.pack()

        tk.Label(self.left_panel, text="Grado del árbol:").pack()
        self.tree_degree_entry = tk.Entry(self.left_panel)
        self.tree_degree_entry.pack()

        generate_tree_button = tk.Button(self.left_panel, text="Generar Árbol", command=self.generate_tree)
        generate_tree_button.pack()

        clear_graph_button = tk.Button(self.right_panel, text="Borrar Árbol", command=self.clear_graph)
        clear_graph_button.pack(pady=10)

        clear_graph_button = tk.Button(self.right_panel, text="Mostrar Información del árbol", command=self.show_tree_info)
        clear_graph_button.pack(pady=10)

        is_tree_button = tk.Button(self.right_panel, text="¿Es árbol?", command=self.check_if_tree)
        is_tree_button.pack(pady=10)

        is_balanced_tree_button = tk.Button(self.right_panel, text="¿Es árbol equilibrado?", command=self.check_if_balanced)
        is_balanced_tree_button.pack(pady=10)
        
        is_p_balanced_tree_button = tk.Button(self.right_panel, text="¿Es árbol perfectamente equilibrado?", command=self.check_if_perfectly_balanced)
        is_p_balanced_tree_button.pack(pady=10)

        is_avl_balanced_tree_button = tk.Button(self.right_panel, text="¿Es árbol equilibrado avl?", command=self.check_if_avl)
        is_avl_balanced_tree_button.pack(pady=10)

        is_complete_tree_button = tk.Button(self.right_panel, text="¿Es árbol completo?", command=self.check_if_complete_tree)
        is_complete_tree_button.pack(pady=10)

        is_full_tree_button = tk.Button(self.right_panel, text="¿Es árbol lleno?", command=self.check_if_full_binary_tree)
        is_full_tree_button.pack(pady=10)

        self.create_expression_button = tk.Button(self.right_panel, text="Crear Expresión", command=self.create_expression)
        self.create_expression_button.pack(pady=10)

        tk.Label(self.left_panel, text="Nodo inicio camino:").pack()
        self.start_node_entry = tk.Entry(self.left_panel)
        self.start_node_entry.pack()

        tk.Label(self.left_panel, text="Nodo fin camino:").pack()
        self.end_node_entry = tk.Entry(self.left_panel)
        self.end_node_entry.pack()

        undo_button = tk.Button(self.right_panel, text="Deshacer", command=self.undo)
        undo_button.pack(pady=10)

        redo_button = tk.Button(self.right_panel, text="Rehacer", command=self.redo)
        redo_button.pack(pady=10)

        find_path_button = tk.Button(self.left_panel, text="Encontrar Camino", command=self.find_path)
        find_path_button.pack()

        ttk.Separator(self.root, orient='vertical').pack(side='left', fill='y', padx=10)

        # Lienzo para dibujar el grafo
        self.figure = Figure(figsize=(8, 6))
        self.canvas = FigureCanvasTkAgg(self.figure, master=self.root)
        self.canvas.get_tk_widget().pack(side=tk.LEFT, fill=tk.BOTH, expand=1)
        self.ax = self.figure.add_subplot(111)

        self.draw_graph(self.graph.graph)

        # Habilitar el arrastre de nodos
        self.node_drag = None
        self.canvas.mpl_connect('button_press_event', self.on_press)
        self.canvas.mpl_connect('motion_notify_event', self.on_motion)
        self.canvas.mpl_connect('button_release_event', self.on_release)
    
    def draw_graph(self, graph):
        self.ax.clear()
        pos = graphviz_layout(graph, prog="dot")
        node_colors = [graph.nodes[node].get('color', 'skyblue') for node in graph.nodes]
        nx.draw(graph, pos, with_labels=True, node_size=700, node_color=node_colors, font_size=10, font_weight="bold", ax=self.ax)
        nx.draw_networkx_edge_labels(graph, pos, edge_labels=self.graph.edge_labels, ax=self.ax)
        self.canvas.draw()

    def draw_expression_tree(self, expression_tree, root_node):
        self.ax.clear()
        graph = expression_tree
        pos = graphviz_layout(graph, prog="dot")
        node_colors = [graph.nodes[node].get('color', 'skyblue') for node in graph.nodes]
        nx.draw(graph, pos, with_labels=True, node_size=700, node_color=node_colors, font_size=10, font_weight="bold", ax=self.ax)
        nx.draw_networkx_nodes(graph, pos, nodelist=[root_node], node_color='red', node_size=700)
        self.canvas.draw()

    def clear_graph(self):
        self.graph.graph.clear()
        self.graph.edge_labels.clear()
        self.graph.edge_count = 0
        self.draw_graph(self.graph.graph)

    def show_tree_info(self):
        tree_info = self.get_tree_info()
        messagebox.showinfo("Información del Árbol", tree_info)

    def get_tree_info(self):
        num_nodes = len(self.graph.graph.nodes)
        num_edges = len(self.graph.graph.edges)
        tree_root = None
        internal_nodes = []
        leaf_nodes = []

        # Encontrar la raíz del árbol (el nodo que no tiene ningún padre)
        for node in self.graph.graph.nodes:
            if not any(node in edge[1:] for edge in self.graph.graph.edges):
                tree_root = node
                break

        # Encontrar los nodos internos y las hojas
        for node in self.graph.graph.nodes:
            neighbors = list(self.graph.graph.neighbors(node))
            if neighbors and node != tree_root:
                if len(neighbors) == 1:
                    leaf_nodes.append(node)
                else:
                    internal_nodes.append(node)
            elif not neighbors and node != tree_root:
                leaf_nodes.append(node)

        info = "Información del Árbol:\n\n"
        info += f"Raíz del árbol: {tree_root}\n"
        info += f"Nodos internos: {', '.join(internal_nodes)}\n"
        info += f"Hojas del árbol: {', '.join(leaf_nodes)}\n"
        info += f"Número total de nodos: {num_nodes}\n"
        info += f"Número total de aristas: {num_edges}\n"
        return info        

    def create_expression(self):
        expression = askstring("Crear Expresión", "Ingrese la expresión matemática:")
        if expression:
            try:
                postfix_expression = self.graph.infix_to_postfix(expression.split())
                messagebox.showinfo("Expresión Postfija", f"La expresión postfija es: {' '.join(postfix_expression)}")
                self.show_expression_tree(postfix_expression)
                messagebox.showinfo("El resultado de la expresión es", f"Resultado es: {eval(expression)}")
            except Exception as e:
                messagebox.showerror("Error", f"No se pudo crear la expresión postfija: {str(e)}")          

    def build_expression_tree(self, postfix_expression):
            stack = []
            expression_tree = nx.DiGraph()

            for token in postfix_expression:
                if token in ['+', '-', '*', '/', '^']:
                    operand2 = stack.pop()
                    operand1 = stack.pop()
                    expression_tree.add_node(token)
                    expression_tree.add_edge(token, operand1)
                    expression_tree.add_edge(token, operand2)
                    stack.append(token)
                else:
                    expression_tree.add_node(token)
                    stack.append(token)

            root_node = stack.pop()
            return expression_tree, root_node

    def show_expression_tree(self, postfix_expression):
        try:
            expression_tree, root_node = self.graph.build_expression_tree(postfix_expression)
            self.draw_expression_tree(expression_tree, root_node)
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo construir el árbol de expresión: {str(e)}")

    def check_if_tree(self):
        is_tree = self.graph.is_tree()
        if is_tree:
            messagebox.showinfo("Resultado", "El grafo es un árbol")
        else:
            messagebox.showinfo("Resultado", "El grafo no es un árbol")
            
    def check_if_full_binary_tree(self):
        is_full = self.graph.is_full_binary_tree()
        if is_full:
            messagebox.showinfo("Resultado", "El árbol es un árbol lleno")
        else:
            messagebox.showinfo("Resultado", "El árbol no es un árbol lleno")
    
    def check_if_balanced(self):
        is_balanced = self.graph.is_balanced()
        if is_balanced:
            messagebox.showinfo("Resultado", "El árbol es un árbol equilibrado")
        else:
            messagebox.showinfo("Resultado", "El árbol no es un árbol equilibrado")
    
    def check_if_perfectly_balanced(self):
        is_perfectly_balanced = self.graph.is_perfectly_balanced()
        if is_perfectly_balanced:
            messagebox.showinfo("Resultado", "El árbol es un árbol perfectamente equilibrado")
        else:
            messagebox.showinfo("Resultado", "El árbol no es un árbol perfectamente equilibrado")
            
    def check_if_avl(self):
        is_avl = self.graph.is_avl()
        if is_avl:
            messagebox.showinfo("Resultado", "El árbol es un árbol AVL equilibrado")
        else:
            messagebox.showinfo("Resultado", "El árbol no es un árbol AVL equilibrado")

    def check_if_complete_tree(self):
        is_complete = self.graph.is_complete_tree()
        if is_complete:
            messagebox.showinfo("Resultado", "El árbol es un árbol completo")
        else:
            messagebox.showinfo("Resultado", "El árbol no es un árbol completo")

    def add_node(self):
        new_node_name = self.node_entry.get()
        if new_node_name:
            self.graph.add_node(new_node_name)
            self.node_entry.delete(0, tk.END)
            self.draw_graph(self.graph.graph)

    def remove_node(self):
        node_name = self.node_remove_entry.get()
        if node_name:
            self.graph.remove_node(node_name)
            self.node_remove_entry.delete(0, tk.END)
            self.draw_graph(self.graph.graph)

    def add_edge(self):
        node1 = self.node1_entry.get()
        node2 = self.node2_entry.get()
        if node1 and node2:
            self.graph.add_edge(node1, node2)
            self.node1_entry.delete(0, tk.END)
            self.node2_entry.delete(0, tk.END)
            self.draw_graph(self.graph.graph)

    def remove_edge(self):
        edge_name = self.edge_remove_entry.get()
        if edge_name:
            self.graph.remove_edge(edge_name)
            self.edge_remove_entry.delete(0, tk.END)
            self.draw_graph(self.graph.graph)

    def generate_tree(self):
        level = int(self.tree_level_entry.get())
        degree = int(self.tree_degree_entry.get())
        self.graph.generate_tree(level, degree)
        self.draw_graph(self.graph.graph)

    def generate_tree(self):
        try:
            degree = int(self.tree_degree_entry.get().strip())
            levels = int(self.tree_level_entry.get().strip())
            self.graph.generate_tree(degree, levels)
            self.draw_graph(self.graph.graph)
        except ValueError:
            messagebox.showerror("Error", "Por favor, ingrese valores numéricos válidos para el grado y los niveles del árbol")

    def find_path(self):
        start_node = self.start_node_entry.get()
        end_node = self.end_node_entry.get()

        if start_node and end_node:
            path = self.graph.bfs_camino(start_node, end_node)
            if path:
                self.draw_graph(self.graph.graph)
                messagebox.showinfo("El camino de " + start_node + " a " + end_node, f"El camino es: {' -> '.join(path)}")
            else:
                messagebox.showwarning("Sin camino", "No se encontró un camino entre los nodos especificados")
        else:
            messagebox.showwarning("Advertencia", "Los nombres de los nodos de inicio y fin no pueden estar vacíos")

    def undo(self):
        self.graph.undo()
        self.draw_graph(self.graph.graph)

    def redo(self):
        self.graph.redo()
        self.draw_graph(self.graph.graph)

    def on_press(self, event):
        if event.inaxes != self.ax:
            return
        for node, (x, y) in self.graph.pos.items():
            if (event.xdata - x)**2 + (event.ydata - y)**2 < 0.01:
                self.node_drag = node
                break

    def on_motion(self, event):
        if self.node_drag is None:
            return
        if event.inaxes != self.ax:
            return
        self.graph.pos[self.node_drag] = (event.xdata, event.ydata)
        self.draw_graph(self.graph.graph)

    def on_release(self, event):
        self.node_drag = None


class Portada:
    def __init__(self, root):
        self.root = root
        self.root.title("Programa Árboles")
        self.root.geometry("1280x800")

        self.label = tk.Label(self.root, text="Programa de Árboles Unidad 4 Teoría de Grafos", font=("Arial", 20))
        self.label.pack(pady=50)

        self.label = tk.Label(self.root, text="Presentado por: Luis Carlos Calderón Calvo - Andres Felipe Zuñiga", font=("Arial", 12))
        self.label.pack(pady=50)

        self.label = tk.Label(self.root, text="Presentado a: Ph.D Pedro Pablo Cárdenaz Alzate", font=("Arial", 12))
        self.label.pack(pady=50)

        self.label = tk.Label(self.root, text="Año: 2024", font=("Arial", 12))
        self.label.pack(pady=50)

        self.start_button = tk.Button(self.root, text="Empezar", command=self.start_graph_gui, font=("Arial", 15))
        self.start_button.pack(pady=20)

        self.exit_button = tk.Button(self.root, text="Salir", command=self.root.quit, font=("Arial", 15))
        self.exit_button.pack(pady=10)

    def start_graph_gui(self):
        self.fade_out()
        self.root.after(2000, self.initialize_graph_gui)  # Ajusta el tiempo de espera según la duración de la animación

    def fade_out(self):
        alpha = self.root.attributes("-alpha")
        if alpha > 0:
            alpha -= 0.05
            self.root.attributes("-alpha", alpha)
            self.root.after(50, self.fade_out)  # Ajusta la velocidad de la animación

    def initialize_graph_gui(self):
        self.root.destroy()  # Cerrar la ventana de la portada
        new_root = tk.Tk()  # Crear una nueva ventana
        graph = Graph()
        GraphGUI(new_root, graph)  # Iniciar la interfaz de GraphGUI en la nueva ventana
        new_root.mainloop()

if __name__ == "__main__":
    root = tk.Tk()
    portada = Portada(root)
    root.mainloop()