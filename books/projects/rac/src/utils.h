#ifndef UTILS_H
#define UTILS_H

#include <cassert>
#include <deque>
#include <ostream>
#include <vector>

#define UNREACHABLE() assert (!"Woopsie, some unreachable code was reach")

//***********************************************************************************
// Linked Lists
//***********************************************************************************

template <class T> class List
{
public:
  T *value;
  List<T> *next;

  List<T> (T *v, List<T> *n = nullptr)
  {
    value = v;
    next = n;
  }
  List<T> (T *v1, T *v2)
  {
    value = v1;
    next = new List<T> (v2);
  }

  static List<T> *
  empty ()
  {
    return nullptr;
  }

  unsigned length ();
  List<T> *nthl (unsigned n);
  T *nth (unsigned n);
  T *find (const char *name);
  bool isMember (T *ptr);
  List<T> *add (T *value);
  List<T> *push (T *value);
  List<T> *pop ();
  List<T> *copy ();
  void displayList (std::ostream &os, unsigned indent = 0) const;
  void displayDefs (std::ostream &os) const;

  T *
  first ()
  {
    return value;
  }
};

template <typename T>
List<T> *
to_list (std::vector<T *> v)
{

  List<T> *res = nullptr;
  for (auto elm : v)
    {
      if (res)
        res->add (elm);
      else
        res = new List (elm);
    }
  return res;
}

template <typename T>
std::vector<T *>
collect (List<T> *l)
{
  std::vector<T *> res;
  for_each (l, [&res] (T *elm) { res.push_back (elm); });
  return res;
}

template <class T> class BetterList
{
public:
  BetterList<T> () : l_ (nullptr) {}

  BetterList<T> (T *v, List<T> *n = nullptr) : l_ (v, n) {}

  BetterList<T> (T *v1, T *v2) : l_ (v1, v2) {}

  bool
  is_empty () const
  {
    return l_ == nullptr;
  }

  unsigned
  length ()
  {
    if (l_)
      return l_->length ();
    else
      return 0;
  }

  List<T> *
  nthl (unsigned n)
  {
    assert (l_);
    return l_->nthl (n);
  }
  T *
  nth (unsigned n)
  {
    assert (l_);
    return l_->nth (n);
  }
  T *
  find (const char *name)
  {
    assert (l_);
    return l_->find (name);
  }
  bool
  isMember (T *ptr)
  {
    assert (l_);
    return l_->isMember (ptr);
  }
  List<T> *
  add (T *value)
  {
    return l_->add (value);
  }
  List<T> *
  push (T *value)
  {
    assert (l_);
    return l_->push (value);
  }
  List<T> *
  pop ()
  {
    assert (l_);
    return l_->pop ();
  }
  List<T> *
  copy ()
  {
    assert (l_);
    return l_->copy ();
  }
  void
  displayList (std::ostream &os, unsigned indent = 0) const
  {
    assert (l_);
    l_->displayList (os, indent);
  }
  void
  displayDefs (std::ostream &os) const
  {
    assert (l_);
    l_->displayDefs (os);
  }

  T *
  first ()
  {
    assert (l_);
    return l_->value;
  }

  List<T> *
  _underlying ()
  {
    assert (l_);
    return l_;
  }

  List<T> *
  _move_underlying ()
  {
    auto l = static_cast<List<T> *> (nullptr);
    std::swap (l, l_);
    return l_;
  }

  static BetterList<T>
  _from_raw (List<T> *l)
  {
    BetterList<T> b;
    b.l_ = l;
    return b;
  }

private:
  List<T> *l_;
};

template <typename T, typename F>
void
for_each (List<T> *list, F f)
{
  for (; list; list = list->next)
    {
      f (list->first ());
    }
}

template <typename T, typename F>
void
for_each (BetterList<T> list, F f)
{
  for_each (list._underlying (), f);
}

// Length of a list;

template <class T>
unsigned
List<T>::length ()
{
  unsigned result = 0;
  List<T> *ptr = this;
  while (ptr)
    {
      result++;
      ptr = ptr->next;
    }
  return result;
}

// nth sublist of a list;

template <class T>
List<T> *
List<T>::nthl (unsigned n)
{
  List<T> *ptr = this;
  while (ptr && n)
    {
      ptr = ptr->next;
      n--;
    }
  return ptr;
}

// nth element of a list;

template <class T>
T *
List<T>::nth (unsigned n)
{
  return this->nthl (n)->value;
}

// Add a new element to the end of a list:

template <class T>
List<T> *
List<T>::add (T *value)
{
  List<T> *ptr = this;
  while (ptr->next)
    {
      ptr = ptr->next;
    }
  ptr->next = new List<T> (value);
  return this;
}

// Add a new element to the front of a list and return a pointer to the new
// list:

template <class T>
List<T> *
List<T>::push (T *value)
{
  return new List<T> (value, this);
}

// Find an element in the list with a given name:

template <class T>
T *
List<T>::find (const char *name)
{
  List<T> *ptr = this;
  while (ptr)
    {
      if (!strcmp (ptr->value->getname (), name))
        {
          return ptr->value;
        }
      ptr = ptr->next;
    }
  return nullptr;
}

// Find a given object in a list:

template <class T>
bool
List<T>::isMember (T *ptr)
{
  List<T> *lst = this;
  while (lst)
    {
      if (lst->value == ptr)
        {
          return true;
        }
      lst = lst->next;
    }
  return false;
}

// Remove the head of a list and return a pointer to the tail:

template <class T>
List<T> *
List<T>::pop ()
{
  List<T> *result = this->next;
  delete this;
  return result;
}

// Create a copy of a list:

template <class T>
List<T> *
List<T>::copy ()
{
  List<T> *result = new List<T> (value);
  List<T> *ptr = next;
  while (ptr)
    {
      result->add (ptr->value);
      ptr = ptr->next;
    }
  return result;
}

// Call "display" on each element of a list:

template <class T>
void
List<T>::displayList (std::ostream &os, unsigned indent) const
{
  const List<T> *ptr = this;
  while (ptr)
    {
      ptr->value->display (os, indent);
      ptr = ptr->next;
    }
}

// Call "displayDef" on each element of a list:

template <class T>
void
List<T>::displayDefs (std::ostream &os) const
{
  List<T> *ptr = this;
  while (ptr)
    {
      ptr->value->displayDef (os);
      ptr = ptr->next;
    }
}

// BigList: a list with a pointer to the last entry, designed for a fast add
// operation

template <class T> class BigList
{
  List<T> *front_;
  List<T> *back_;

public:
  BigList<T> (T *v) : front_ (new List<T> (v)), back_ (front_) {}

  BigList<T> *
  add (T *v)
  {
    back_->next = new List<T> (v);
    back_ = back_->next;
    return this;
  }

  List<T> *
  front ()
  {
    return front_;
  }
};

// Stacks:

template <typename T> class SymbolStack
{
  // We use a deque to store all values and we use nullptr to mark the limit
  // between frames. All values are sorted from last to be pushed to first
  // (this is done cheaply by deque push_front()) and thus searching should be
  // more or less efficient (we are traversing the addresses from low to high).
public:
  void
  push (T *value)
  {
    assert (value && "this stack does not support nullptr ias value");
    data_.push_front (value);
  }

  void
  pushFrame ()
  {
    data_.push_front (nullptr);
  }

  void
  popFrame ()
  {
    // While there is some values in the vector and the last one is not null
    // (the end of the last frame), we remove the element of the last frame.
    while (data_.size () && data_.front ())
      {
        data_.pop_front ();
      }
  }

  T *
  find_last_frame (const char *name)
  {
    for (auto it = begin (data_); it != end (data_); ++it)
      {
        // Detect the limit of frame and stop.
        if (!*it)
          {
            break;
          }

        if (!strcmp ((*it)->getname (), name))
          {
            return *it;
          }
      }
    return nullptr;
  }

  T *
  find (const char *name)
  {
    for (auto it = begin (data_); it != end (data_); ++it)
      {
        // Detect the limit of frame and ingore it.
        if (!*it)
          {
            continue;
          }

        if (!strcmp ((*it)->getname (), name))
          {
            return *it;
          }
      }
    return nullptr;
  }

private:
  std::deque<T *> data_;
};

#endif // UTILS_H
