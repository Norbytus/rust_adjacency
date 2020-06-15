use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::{Debug, Display};

#[derive(Debug)]
pub enum AdjacencyListsError {
    UndefinedVertex,
}

pub type AdjacencyListsResult<T> = Result<T, AdjacencyListsError>;

impl Display for AdjacencyListsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            AdjacencyListsError::UndefinedVertex => write!(f, "Undefined vertex")
        }
    }
}

#[derive(Debug)]
pub struct AdjacencyLists<T: Hash + Eq + Debug>(HashMap<T, Vec<Edge<T>>>);

impl<T: Hash + Eq + Debug> AdjacencyLists<T> {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn add_vertex(&mut self, vertex: T) {
        self.0.insert(vertex, Vec::new());
    }

    pub fn add_vertexes(&mut self, vertexes: Vec<T>) {
        for vertex in vertexes {
            self.0.insert(vertex, Vec::new());
        }
    }

    pub fn add_neighborhoods(&mut self, src: T, edges: Vec<Edge<T>>) -> AdjacencyListsResult<()> {

        for edge in edges {
            if !self.is_vertex_exist(edge.get_value()) {
                return Err(AdjacencyListsError::UndefinedVertex)
            }

            if let Some(node) = self.0.get_mut(&src) {
                node.push(edge);
            }
        }

        Ok(())
    }

    fn is_vertex_exist(&self, node: &T) -> bool {
        self.0.contains_key(node)
    }

    pub fn get_vertex_neighborhoods(&self, node: &T) -> Option<&Vec<Edge<T>>> {
        match self.0.get(node) {
            Some(data) => Some(data),
            None => None,
        }
    }

    pub fn vertex_count(&self) -> usize {
        self.0.len()
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum Edge<T: Hash + Eq + Debug> {
    Direct(T),
    Undirected(T),
    DirectWeight(T, i64),
    UndirectedWeight(T, i64),
}

impl<T: Hash + Eq + Debug> Edge<T> {
    pub fn get_value(&self) -> &T {
        match self {
            Self::Direct(value) => value,
            Self::Undirected(value) => value,
            Self::DirectWeight(value, _) => value,
            Self::UndirectedWeight(value, _) => value,
        }
    }
}

pub fn dfs<'a, T: Hash + Eq + Debug>(
    start: &'a T,
    graph: &'a AdjacencyLists<T>,
    visited: &mut Vec<&'a T>)
{

    if visited.contains(&start) {
        return;
    }

    visited.push(start);
    if let Some(neighborhoods) = graph.get_vertex_neighborhoods(&start) {
        for neighbor in neighborhoods {
            dfs(neighbor.get_value(), graph, visited);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_vertex() {
        let mut graph: AdjacencyLists<i32> = AdjacencyLists::new();
        graph.add_vertex(12);

        assert_eq!(graph.vertex_count(), 1);
    }

    #[test]
    fn success_add_neighborhoods() {
        let mut graph: AdjacencyLists<i32> = AdjacencyLists::new();
        graph.add_vertex(12);
        graph.add_vertex(13);
        let _ = graph.add_neighborhoods(12, vec![Edge::Undirected(13)]);

        assert_eq!(graph.vertex_count(), 2);
        assert_eq!(
            graph.get_vertex_neighborhoods(&12),
            Some(&vec![Edge::Undirected(13)])
        );
    }

    #[test]
    fn add_not_exist_neighborhoods() {
        let mut graph: AdjacencyLists<i32> = AdjacencyLists::new();
        graph.add_vertex(12);
        let error = graph.add_neighborhoods(12, vec![Edge::Undirected(13)]);
        assert!(error.is_err());
        assert_eq!(graph.vertex_count(), 1);
    }

    #[test]
    fn node_map() {
        let mut graph: AdjacencyLists<i32> = AdjacencyLists::new();
        graph.add_vertexes(vec![1, 7, 5, 6, 9]);

        let _ = graph.add_neighborhoods(
            1,
            vec![Edge::Undirected(7), Edge::Undirected(5), Edge::Undirected(6)]
        );

        let _ = graph.add_neighborhoods(
            7,
            vec![Edge::Undirected(1), Edge::Undirected(5)]
        );

        let _ = graph.add_neighborhoods(
            5,
            vec![Edge::Undirected(6), Edge::Undirected(7), Edge::Undirected(1)]
        );

        let _ = graph.add_neighborhoods(
            6,
            vec![Edge::Undirected(5), Edge::Undirected(1)]
        );

        let mut visited = Vec::new();
        dfs(&6, &graph, &mut visited);
        dbg!(visited);
    }

    #[test]
    fn dfs_visited() {
        let mut graph: AdjacencyLists<i32> = AdjacencyLists::new();
        graph.add_vertexes(vec![1, 7, 5, 6, 9]);

        let _ = graph.add_neighborhoods(
            1,
            vec![Edge::Undirected(7), Edge::Undirected(5), Edge::Undirected(6)]
        );

        let _ = graph.add_neighborhoods(
            7,
            vec![Edge::Undirected(1), Edge::Undirected(5)]
        );

        let _ = graph.add_neighborhoods(
            5,
            vec![Edge::Undirected(6), Edge::Undirected(7), Edge::Undirected(1)]
        );

        let _ = graph.add_neighborhoods(
            6,
            vec![Edge::Undirected(5), Edge::Undirected(1)]
        );

        let mut visited = Vec::new();
        dfs(&1, &graph, &mut visited);
        assert_eq!(visited, vec![&1, &7, &5, &6]);
    }
}
