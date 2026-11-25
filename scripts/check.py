"""Check the conjecture on complete bipartite graphs, using exact certificates."""
from collections import deque
from itertools import combinations


def test(n):
    adjacency = [set(range(2, 2 + n)) for _ in range(2)] + [{0, 1} for _ in range(n)]
    distances = []
    for source in range(n + 2):
        row = [-1] * (n + 2)
        row[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if row[v] < 0:
                    row[v] = row[u] + 1
                    queue.append(v)
        assert min(row) >= 0
        distances.append(row)
    tri = max(distances[u][v] + distances[v][w] + distances[w][u]
              for u, v, w in combinations(range(n + 2), 3))
    independent = set(range(2, n + 2))
    assert all(v not in adjacency[u] for u, v in combinations(independent, 2))
    parts = [[0, 2], [1, 3]] + [[v] for v in range(4, n + 2)]
    assert sorted(v for part in parts for v in part) == list(range(n + 2))
    assert all(v in adjacency[u] for part in parts for u, v in combinations(part, 2))
    assert len(parts) == len(independent)
    eulerian = all(len(row) % 2 == 0 for row in adjacency)
    return tri, len(parts), eulerian


if __name__ == '__main__':
    for n in range(2, 26, 2):
        tri, cover, eulerian = test(n)
        assert eulerian and cover == n and tri == (4 if n == 2 else 6)
        print(f'K(2,{n}): Eulerian={eulerian}, triameter={tri}, clique cover={cover}, '
              f'bound holds={cover <= tri + 4}')
