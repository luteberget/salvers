use std::collections::HashMap;

/// A binary **min** heap of i32 keys. Each method that modifies the heap takes a function
/// parameter for assigning a value to each key for comparison. This function should
/// be consistent over calls to ensure correct heap properties.
pub struct OrderHeap {
    heap: Vec<i32>,             // Heap of variables
    indices: HashMap<i32, i32>, // Map of variables to index in heap
}

impl OrderHeap {
    /// Empty heap.
    pub fn new() -> Self {
        OrderHeap {
            heap: Vec::new(),
            indices: HashMap::new(),
        }
    }

    /// Clear the heap.
    pub fn clear(&mut self) {
        self.heap.clear();
        self.indices.clear();
    }

    /// Does the heap have any elements?
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn left(i: i32) -> i32 {
        i * 2 + 1
    }
    fn right(i: i32) -> i32 {
        (i + 1) * 2
    }
    fn parent(i: i32) -> i32 {
        (i - 1) >> 1
    }

    fn percolate_up(&mut self, mut i: i32, value: impl Fn(&i32) -> i32) {
        let var = self.heap[i as usize];
        let mut p = Self::parent(i);
        while i != 0 && value(&var) < value(&self.heap[p as usize]) {
            self.heap[i as usize] = self.heap[p as usize];
            self.indices.insert(self.heap[p as usize], i);
            i = p;
            p = Self::parent(p);
        }

        self.heap[i as usize] = var;
        self.indices.insert(var, i);
    }

    fn percolate_down(&mut self, mut i: i32, value: impl Fn(&i32) -> i32) {
        let var = self.heap[i as usize];
        while (Self::left(i) as usize) < self.heap.len() {
            let child = if (Self::right(i) as usize) < self.heap.len()
                && value(&self.heap[Self::right(i) as usize])
                    < value(&self.heap[Self::left(i) as usize])
            {
                Self::right(i)
            } else {
                Self::left(i)
            };

            if !(value(&self.heap[child as usize]) < value(&var)) {
                break;
            }

            self.heap[i as usize] = self.heap[child as usize];
            self.indices.insert(self.heap[i as usize], i);
            i = child;
        }
        self.heap[i as usize] = var;
        self.indices.insert(var, i);
    }

    /// Does the heap contain the given key?
    pub fn contains(&self, var: i32) -> bool {
        self.indices.contains_key(&var)
    }

    /// Insert the given key into the heap.
    pub fn insert(&mut self, key: i32, value: impl Fn(&i32) -> i32) {
        self.indices.insert(key, self.heap.len() as i32);
        self.heap.push(key);
        self.percolate_up(self.heap.len() as i32 - 1, value);
    }

    /// Borrow the minimum element of the heap, or `None` if the heap is empty.
    pub fn peek(&self) -> Option<&i32> {
        self.heap.get(0)
    }

    /// Remove the minimum element from the heap and return it, or `None` if the heap is empty.
    pub fn remove_min(&mut self, value: impl Fn(&i32) -> i32) -> Option<i32> {
        if self.is_empty() {
            return None;
        }
        let var = self.heap.swap_remove(0);
        self.indices.insert(self.heap[0], 0);
        self.indices.remove(&var);
        if self.heap.len() > 1 {
            self.percolate_down(0, value);
        }
        Some(var)
    }

    // TODO
    //pub fn rebuild ?
}
