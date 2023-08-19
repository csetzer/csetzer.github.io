#include <iostream>
#include <string>


//Function types

template<typename X,typename Y> class ar{
public:
 virtual  Y operator()(X x)=0;
};

#define Ar(X,Y) ar<X,Y>*


//the type of functions with no arguments

template<typename Y> class void_ar{
public:
 virtual  Y operator()()=0;
};

#define Void_Ar(X) void_ar<X>*



//We define plus : int -> int-> int
//          plus = \int x. \int y. int x+y

class plus_aux_aux: public ar<int,int>{
  int first_arg;
public:
  plus_aux_aux(int x){
    first_arg = x;
  };

  int operator()(int y){
    return first_arg + y;
  };
};

class plus_aux: public ar<int,Ar(int,int)>{
public:
  Ar(int,int) operator()(int x){
    return new plus_aux_aux(x);
  };
};

Ar(int,Ar(int,int)) plus = new plus_aux();




//Definition of lazy

template<typename X> class lazy{
  bool is_evaluated;
  union {
    X result; 
    Void_Ar(X) compute_function;};
public:
  lazy(Void_Ar(X) compute_function){
    is_evaluated = false;
    this->compute_function = compute_function;
  };

  X eval(){
    if (not is_evaluated){
      result = (* compute_function)();
      is_evaluated = true;
    };
    return result;
  };
};

#define Lazy(X) lazy<X>*

//Creation of Lazy(X) from lambda terms
  
template<typename X> Lazy(X) create_lazy
 (Void_Ar(X) compute_function){
  return new lazy<X>(compute_function);
};


//eval takes a lazy element and computes its content

template<typename X> X eval(Lazy(X) x){
  return x->eval();
};


//We convert an element of X into an element of Lazy(X)


// value_to_lazy(X y) is 
// create_lazy(\ void x.X y)


template<typename X>class value_to_lazy_aux: public void_ar<X>{
  X known_result;
public:
  value_to_lazy_aux(X known_result){
    this-> known_result = known_result;
  };

  X operator()(){
    return known_result;
  };
};


template<typename X>Void_Ar(X) value_to_lazy_aux2(X x){
  return new value_to_lazy_aux<X>(x);
};


template<typename X>Lazy(X) value_to_lazy(X x){
  return create_lazy(value_to_lazy_aux2(x));
};





//We define lazy_apply<X,Y> : (X->Y) -> Lazy(X) -> Lazy(Y)
//lazy_apply<X,Y> (f,a) = 
//   create_lazy(\ void. Y f ^^ eval(a))

template <typename X,typename Y>class lazy_apply_aux: public void_ar<Y>{
  Ar(X,Y) f;
  Lazy(X) a;
  
public:
  lazy_apply_aux(Ar(X,Y) f,
		 Lazy(X) a){
    this-> f = f;
    this-> a = a;
  };

  Y operator()(){
    return( (*f)( eval(a)));
  };
};

  
template <typename X,typename Y>Lazy(Y) lazy_apply(Ar(X,Y) f,
						   Lazy(X) a){
  return create_lazy(new lazy_apply_aux<X,Y>(f,a));
};
  



//We define lazy streams



template<typename X>class lazy_stream{
public:
  Lazy(X) head;
  Lazy(lazy_stream<X>*) tail;
  lazy_stream(Lazy(X) head,Lazy(lazy_stream<X>*) tail){
    this-> head = head;
    this-> tail = tail;
  };
};

#define Lazy_Stream(X) lazy_stream<X>*


//A cons operation on lazy_stream

template<typename X>Lazy_Stream(X) lazy_cons(Lazy(X) head,
					      Lazy(lazy_stream<X> *) tail){
  return new lazy_stream<X>(head,tail);
};

//A cons operation creating Lazy(Lazy_Stream(X) )
//This is 
//lazy_cons_lazy(head,tail) = 
//    create_lazy(\ void. Lazy_Stream(X) lazy_cons(head,tail))

template<typename X>class lazy_cons_lazy_aux: public void_ar<Lazy_Stream(X)>{
  Lazy(X) head;
  Lazy(Lazy_Stream(X)) tail;
 public:
  lazy_cons_lazy_aux(Lazy(X) head,
		     Lazy(Lazy_Stream(X)) tail){
    this-> head = head;
    this-> tail = tail;
  };

  Lazy_Stream(X) operator()(){
    return lazy_cons(head,tail);
  };
};

template<typename X>Lazy(Lazy_Stream(X)) lazy_cons_lazy
           (Lazy(X) head,
	    Lazy(Lazy_Stream(X)) tail){
  return create_lazy
               (new lazy_cons_lazy_aux<X>(head,tail));
};



//We compute the tail of a lazy_stream which is trivially

template<typename X>Lazy(Lazy_Stream(X)) lazy_tail(Lazy_Stream(X) x){
  return x->tail;
};

//the tail of an element of Lazy(lazy_stream<X>)
//
//lazy_tail<X>(s) = 
//   create_lazy(\ void x.eval(eval(s)->tail));

template<typename X>class lazy_tail_aux: public void_ar<Lazy_Stream(X)>{
  Lazy(Lazy_Stream(X)) arg;
public:
  lazy_tail_aux(Lazy(Lazy_Stream(X)) arg){
    this->arg = arg;
  };

  Lazy_Stream(X) operator()(){
    return eval(eval(arg)->tail);
  };

};


template<typename X>Lazy(Lazy_Stream(X)) lazy_tail(Lazy(Lazy_Stream(X)) x){
  return create_lazy(new lazy_tail_aux<X>(x));
};


//We define zip_with lazily
//lazy_zip_with<X,Y,Z>(f,x,y)=
//   create_lazy(\ void x.Lazy_Stream(X) lazy_cons(lazy_apply(f,
//                                                               eval(x),
//                                                 lazy_zip_with<X,Y,Z>(f,(eval x)->tail, (eval y)-> tail)))


template <typename X, typename Y, typename Z>
  class  lazy_zip_with_aux: public void_ar<Lazy_Stream(X)> {
    Ar(X,Ar(Y,Z)) f;
    Lazy(Lazy_Stream(X)) first_list;
    Lazy(Lazy_Stream(X)) second_list;
public:
    lazy_zip_with_aux(Ar(X,Ar(Y,Z)) f,
		      Lazy(Lazy_Stream(X)) first_list,
		      Lazy(Lazy_Stream(X)) second_list){
      this->f = f;
      this->first_list = first_list;
      this->second_list = second_list;};

    Lazy_Stream(X) operator()(){
      Lazy_Stream(X) first_list_eval = eval(first_list);
      Lazy_Stream(X) second_list_eval = eval(second_list);
      Lazy(Ar(Y,Z)) tmp = lazy_apply(f,
				       first_list_eval-> head);
      Lazy(Z) head_result= lazy_apply(eval(tmp),
					 second_list_eval->head);
      return lazy_cons(head_result,
		       create_lazy
		       (new lazy_zip_with_aux
			(f,
			 first_list_eval->tail,
			 second_list_eval-> tail)));
    };
  };


template <typename X, typename Y, typename Z>Lazy(Lazy_Stream(X))   lazy_zip_with
       (Ar(X,Ar(Y,Z)) f,
       Lazy(Lazy_Stream(X)) first_list,
       Lazy(Lazy_Stream(X)) second_list){
  return create_lazy
           (new lazy_zip_with_aux<X,Y,Z>
	    (f,first_list,second_list));
};
		     
  



//We give here the stream range_infinite(begin) = 
//                     [begin,begin+1,begin+2,...]
//

//
//it is defined as
//
//range(n)  = create_lazy(\void x.lazy_cons(value_to_lazy(n),
//                                                 range(n+1)))
class range_infinite_aux: public void_ar<lazy_stream<int>*>{
  int begin;
public:
  range_infinite_aux(int begin){
    this-> begin = begin;
  };

  lazy_stream<int> * operator()(){
    return lazy_cons(value_to_lazy(begin),
			  create_lazy
			  (new range_infinite_aux(begin + 1)));
  };
    
};

Lazy(lazy_stream<int>*) range_infinite(int n){
  return create_lazy(new range_infinite_aux(n));
};


//Here follow the fibonacci numbers

class fib_aux : public void_ar<lazy_stream<int>*>{
public:
  fib_aux(){};
  lazy_stream<int>* operator()(){
    Lazy(int) one_lazy = value_to_lazy(1);
    Lazy(lazy_stream<int>*) this_as_stream 
            = create_lazy(this);
    return eval
            (lazy_cons_lazy
	     (one_lazy,
	      lazy_cons_lazy
	      (one_lazy,
	       lazy_zip_with
	       (plus,
		this_as_stream,
		lazy_tail(this_as_stream))))); 
  };
};

Lazy(lazy_stream<int>*) fib_aux2 
        = create_lazy(new fib_aux());

lazy_stream<int>* fib = eval(fib_aux2);



int main(){
  lazy_stream<int>* myrange = eval(range_infinite(5));
  std::cout << "Simple example: we output the first 3 numbers of [3,4,5,...]" << std::endl;
  std::cout << eval(myrange-> head) << std::endl;
  std::cout << eval(eval(myrange-> tail)->head) << std::endl;
  std::cout << eval(eval(eval(myrange-> tail)->tail)->head) << std::endl;

  std::cout << "Example using lazy_tail" << std::endl;  
  Lazy(lazy_stream<int>*)  example_lazy_tail_aux = lazy_tail(range_infinite(5));
  lazy_stream<int>* example_lazy_tail = eval(example_lazy_tail_aux);
  std::cout << eval(example_lazy_tail-> head) << std::endl;
  std::cout << eval(eval(example_lazy_tail-> tail)->head) << std::endl;
  std::cout << eval(eval(eval(example_lazy_tail-> tail)->tail)->head) << std::endl;

  
  std::cout << "Example using lazy_apply" << std::endl;  

  class plus_5_aux : public ar <int,int>{
  public:
    int operator () (int x){
      return x + 5;
    };
  };

  Ar(int,int) plus_5 = new plus_5_aux();

  Lazy(int) example_lazy_apply = value_to_lazy(5);
  Lazy(int) example_lazy_apply_result = lazy_apply<int,int>(plus_5,
						    example_lazy_apply);
  std::cout << "Result = "<< eval(example_lazy_apply_result) << std::endl;





  std::cout << "Example using lazy_zip_with" << std::endl;  
  Lazy(lazy_stream<int>*) example_zip_with_1 = range_infinite(5);
  Lazy(lazy_stream<int>*) example_zip_with_2 = range_infinite(8);
  Lazy(lazy_stream<int>*) example_zip_with_3
    = lazy_zip_with(plus,example_zip_with_1,example_zip_with_2);
  lazy_stream<int>* example_zip_with_result = eval(example_zip_with_3);
  

  std::cout << eval(example_zip_with_result-> head) << std::endl;
  std::cout << eval(eval(example_zip_with_result-> tail)->head) << std::endl;
  std::cout << eval(eval(eval(example_zip_with_result-> tail)->tail)->head) << std::endl;


  std::cout << "Example fib" << std::endl;  


  std::cout << eval(fib-> head) << std::endl;
  std::cout << eval(eval(fib-> tail)->head) << std::endl;
  std::cout << eval(eval(eval(fib-> tail)->tail)->head) << std::endl;

  lazy_stream<int>* aux = fib;
  for (int i =0;i<100;i++){
    std::cout << "fib("<< i<<")= "<< eval(aux-> head) << std::endl;
    aux = eval(aux->tail);
  };
  
      
};



  
  

  
  
  
  
