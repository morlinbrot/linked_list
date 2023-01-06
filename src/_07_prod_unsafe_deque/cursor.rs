use std::{marker::PhantomData, mem, ptr::NonNull};

use super::{Link, LinkedList, Node};

pub struct CursorMut<'l, T> {
    pub(crate) cur: Link<T>,
    pub(crate) idx: Option<usize>,
    pub(crate) list: &'l mut LinkedList<T>,
}

impl<T> CursorMut<'_, T> {
    pub fn index(&self) -> Option<usize> {
        self.idx
    }

    pub fn current(&mut self) -> Option<&mut T> {
        // SAFETY: Dereferencing is safe b/c of `NonNull` and the methods on `Option`.
        unsafe { self.cur.map(|ptr| &mut (*ptr.as_ptr()).elem) }
    }

    pub fn peek_next(&mut self) -> Option<&mut T> {
        // SAFETY: Dereferencing is safe b/c of `NonNull` and the methods on `Option`.
        unsafe {
            let next = if let Some(cur) = self.cur {
                (*cur.as_ptr()).next
            } else {
                self.list.head
            };

            next.map(|ptr| &mut (*ptr.as_ptr()).elem)
        }
    }

    pub fn peek_prev(&mut self) -> Option<&mut T> {
        // SAFETY: Dereferencing is safe b/c of `NonNull` and the methods on `Option`.
        unsafe {
            let prev = if let Some(cur) = self.cur {
                (*cur.as_ptr()).prev
            } else {
                self.list.tail
            };

            prev.map(|ptr| &mut (*ptr.as_ptr()).elem)
        }
    }

    pub fn move_next(&mut self) {
        if let Some(cur) = self.cur {
            // SAFETY: TODO.
            unsafe {
                self.cur = (*cur.as_ptr()).next;
                if self.cur.is_some() {
                    // There must already be an index if we are at a node.
                    *self.idx.as_mut().unwrap() += 1;
                } else {
                    // We walked into the ghost node.
                    self.idx = None;
                }
            }
        } else if !self.list.is_empty() {
            // We're at the ghost node but can move forward.
            self.cur = self.list.head;
            self.idx = Some(0);
        } else {
            // We're at the ghost and empty so nothing to move to.
        }
    }

    pub fn move_prev(&mut self) {
        if let Some(cur) = self.cur {
            unsafe {
                self.cur = (*cur.as_ptr()).prev;
                if self.cur.is_some() {
                    *self.idx.as_mut().unwrap() -= 1;
                } else {
                    // We walked into the ghost node.
                    self.idx = None;
                }
            }
        } else if !self.list.is_empty() {
            // We're at the ghost node but can move forward.
            self.cur = self.list.tail;
            self.idx = Some(self.list.len - 1);
        } else {
            // We're at the ghost node and nothing to move to.
        }
    }

    pub fn insert_after(&mut self, elem: T) {
        if let Some(cur) = self.cur {
            // SAFETY: The pointers created with `new_unchecked` are not null.
            unsafe {
                let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                    elem,
                    next: None,
                    prev: None,
                })));

                (*new_node.as_ptr()).prev = Some(cur);
                (*cur.as_ptr()).next = Some(new_node);
                self.cur = Some(new_node);
            }

            self.idx = Some(self.idx.unwrap() + 1);
        } else {
            // If at ghost node, we insert at the front if there are nodes or not.
            self.list.push_front(elem);
            self.idx = Some(self.idx.map_or(0, |v| v + 1));
        }
    }

    pub fn split_before(&mut self) -> LinkedList<T> {
        match self.idx {
            // Edge case 1: Cursor is at the ghost node which sits before head (and after tail), e.g. the whole list is before us:
            // We hand out the whole list and become an empty list.
            None => mem::replace(self.list, LinkedList::new()),
            // Edge case 2: Cursor is at the first node: We don't have to do anything and hand out a new empty list.
            Some(0) => LinkedList::new(),
            // Base case: We create a new list from everything before us and hand it out.
            Some(idx) => unsafe {
                let cur = self.cur.unwrap();
                let out_head = self.list.head;
                let out_tail = (*cur.as_ptr()).prev.take();

                if let Some(node) = out_tail {
                    (*node.as_ptr()).next = None;
                }

                let old_len = self.list.len;
                let new_len = old_len - idx;

                self.list.head = Some(cur);
                self.list.len = new_len;
                self.idx = Some(0);

                LinkedList {
                    head: out_head,
                    tail: out_tail,
                    len: old_len - new_len,
                    _marker: PhantomData,
                }
            },
        }
    }

    pub fn split_after(&mut self) -> LinkedList<T> {
        match self.idx {
            None => mem::replace(self.list, LinkedList::new()),
            Some(idx) if idx == self.list.len - 1 => LinkedList::new(),
            Some(idx) => {
                unsafe {
                    let cur = self.cur.unwrap();
                    let out_tail = self.list.tail;
                    let out_head = (*cur.as_ptr()).next.take();

                    if let Some(node) = out_head {
                        (*node.as_ptr()).prev = None;
                    }

                    let old_len = self.list.len;
                    let new_len = idx + 1;

                    self.list.tail = Some(cur);
                    self.list.len = new_len;
                    // No index update needed.

                    LinkedList {
                        head: out_head,
                        tail: out_tail,
                        len: old_len - new_len,
                        _marker: PhantomData,
                    }
                }
            }
        }
    }

    pub fn splice_before(&mut self, mut other: LinkedList<T>) {
        if other.is_empty() {
            return;
        }

        let other_head = other.head.take().unwrap();
        let other_tail = other.tail.take().unwrap();
        let other_len = other.len;

        unsafe {
            if let Some(cur) = self.cur {
                // We could be at index 0, then `prev` will be `None`.
                let prev = (*cur.as_ptr()).prev;

                // Either way, it will become the `prev` of the other list.
                (*other_head.as_ptr()).prev = prev;

                if let Some(prev_node) = prev {
                    (*prev_node.as_ptr()).next = Some(other_head);
                } else {
                    self.list.head = Some(other_head);
                }

                (*other_tail.as_ptr()).next = Some(cur);
                (*cur.as_ptr()).prev = Some(other_tail);
            } else if let Some(tail) = self.list.tail {
                // We're at the ghost node but not empty, append to back.
                (*tail.as_ptr()).next = Some(other_head);
                (*other_head.as_ptr()).prev = Some(tail);
                self.list.tail = Some(other_tail);
            } else {
                // We're empty, other list becomes self.
                let _ = mem::replace(self.list, other);
            }
        }

        self.list.len += other_len;
        self.idx.map_or(other_len - 1, |v| v + other_len);
    }

    pub fn splice_after(&mut self, mut other: LinkedList<T>) {
        if other.is_empty() {
            return;
        }

        let other_head = other.head.take().unwrap();
        let other_tail = other.tail.take().unwrap();
        let other_len = other.len;

        unsafe {
            if let Some(cur) = self.cur {
                // We could be at index 0, then `next` will be `None`.
                let next = (*cur.as_ptr()).next;

                // Either way, it will become the `next` of the other list.
                (*other_tail.as_ptr()).next = next;

                if let Some(next_node) = next {
                    (*next_node.as_ptr()).prev = Some(other_tail);
                } else {
                    self.list.tail = Some(other_tail);
                }

                (*other_head.as_ptr()).prev = Some(cur);
                (*cur.as_ptr()).next = Some(other_head);
            } else if let Some(head) = self.list.head {
                // We're at the ghost node but not empty, append to front.
                (*head.as_ptr()).prev = Some(other_tail);
                (*other_tail.as_ptr()).next = Some(head);
                self.list.head = Some(other_head);
            } else {
                // We're at ghost and empty, other list becomes self.
                let _ = mem::replace(self.list, other);
            }
        }

        self.list.len += other_len;
        // No index update needed.
    }
}
