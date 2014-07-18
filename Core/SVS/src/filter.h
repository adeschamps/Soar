#ifndef FILTER_H
#define FILTER_H

#include <iostream>
#include <string>
#include <list>
#include <map>
#include <sstream>
#include <iterator>

#include "mat.h"
#include "common.h"
#include "change_tracking_list.h"

#include "filter_val.h"
#include "filter_input.h"

#include "sgnode.h"
#include "soar_interface.h"


/*
 Every filter generates a list of filter values as output, even if
 the list is empty or a singleton.
*/
typedef change_tracking_list<filter_val> filter_output;

/*
 A filter parameter set represents one complete input into a filter. It's
 just a list of pairs <parameter name, value>.
*/
typedef std::vector<std::pair<std::string, filter_val*> > filter_params;


/*
 The filter is the basic query unit in SVS. Each filter takes a list of
 parameter sets generated by the filter_input class and produces a single
 output list. Soar can "mix-and-match" filters by plugging their outputs
 into inputs of other filters. This is done by specifying the desired
 filter plumbing on the SVS command link.

 Filter outputs are updated once every output phase. Updating a filter's
 output is recursive: the filter will first request an update on its
 input, which in turn requests updates on all filters feeding into the
 input. Filters should also try to cache outputs when possible to avoid
 unnecessary computation.
*/

class filter
{
    public:
    
        filter(Symbol* root, soar_interface* si, filter_input* in);
        
        virtual ~filter();
        
        void set_status(const std::string& msg);

        void add_output(filter_val* fv){
          output.add(fv);
        }

        void change_output(filter_val* fv){
          output.change(fv);
        }

        void remove_output(filter_val* fv){
          output.remove(fv);
        }

        bool update();


//TODO slightly less ugly hack
        virtual int getAxis()
        {
            return -3;
        }
        
        virtual int getComp()
        {
            return -3;
        }
        
        filter_output* get_output()
        {
          return &output;
        }
        const filter_input* get_input() const
        {
            return input;
        }
        void listen_for_input(filter_input::listener* l)
        {
            input->listen(l);
        }
        void unlisten_for_input(filter_input::listener* l)
        {
            input->unlisten(l);
        }
        void mark_stale(const filter_params* s)
        {
            input->change(s);
        }

        // Classes that inherit from filter are responsible for 
        // handling output

        virtual void get_output_params(filter_val* v, const filter_params*& p) = 0;

    protected:
        virtual void clear_output(){
          output.clear();
        }
        
        virtual bool update_outputs() = 0;

    private:
        filter_input* input;
        filter_output output;
        std::string status;
        soar_interface* si;
        Symbol* root;
        wme* status_wme;
};

template <class T>
class typed_filter : public filter, public sgnode_listener
{
    public:
        typed_filter(Symbol* root, soar_interface* si, filter_input* in)
          : filter(root, si, in)
        {}
        
        /*
         All created filter_vals are owned by the output list and cleaned
         up there, so don't do it here.
        */
        virtual ~typed_filter(){
          std::map<const filter_params*, filter_val*>::iterator i;
          for(i = in2out.begin(); i != in2out.end(); i++){
            T out;
            if(get_filter_val(i->second, out)){
              output_removed(out);
            }
          }
        }

        void get_output_params(filter_val* fv, const filter_params*& p){
          if(!map_get(out2in, fv, p)){
            p = NULL;
          }
        }
        
        void add_output(const filter_params* p, T v){
          filter_val* fv = new filter_val_c<T>(v);
          output_added(v);
          in2out[p] = fv;
          out2in[fv] = p;
          filter::add_output(fv);
        }

        void update_output(const filter_params* p, T v){
          filter_val* fv;
          if(map_get(in2out, p, fv)){
            T old_out;
            if(get_filter_val(fv, old_out)){
              output_removed(old_out);
            }
            set_filter_val(fv, v);
            output_added(v);
            filter::change_output(fv);
          }
        }

        void remove_output(const filter_params* p){
          filter_val* fv;
          if(map_get(in2out, p, fv)){
            in2out.erase(p);
            if(map_get(out2in, fv, p)){
              out2in.erase(fv);
            }
            T out;
            if(get_filter_val(fv, out)){
              output_removed(out);
            }
            filter::remove_output(fv);
          }
        }


        void node_update(sgnode* n, sgnode::change_type t, const std::string& update_info){}

    protected:
        void clear_output(){
          std::map<const filter_params*, filter_val*>::iterator i;
          for(i = in2out.begin(); i != in2out.end(); i++){
            T out;
            if(get_filter_val(i->second, out)){
              output_removed(out);
            }
          }
          in2out.clear();
          out2in.clear();
          filter::clear_output();
        }

        virtual void output_added(T& out){}
        virtual void output_removed(T& out){}

    private:
        // map from an output value to info about that value (source params and filter_val wrapper)
        std::map<const filter_params*, filter_val*> in2out;
        std::map<filter_val*, const filter_params*> out2in;
};

/***********************************************
 * template specialization for sgnode*
 * We want to listen to shape/transform changes
 *   for the nodes and pass the changes to the 
 *   output ctl
 ***********************************************/

template <>
void typed_filter<sgnode*>::output_added(sgnode*& out){
  out->listen(this);
}

template <>
void typed_filter<sgnode*>::output_removed(sgnode*& out){
  out->unlisten(this);
}


template <>
void typed_filter<sgnode*>::node_update(sgnode* n, sgnode::change_type t, const std::string& update_info){
  if(t != sgnode::TRANSFORM_CHANGED && t != sgnode::SHAPE_CHANGED){
    // Only care about transform/shape changes
    return;
  }

  filter_val* fv = new filter_val_c<sgnode*>(n);
  std::map<filter_val*, const filter_params*>::iterator i = out2in.find(fv);
  if(i != out2in.end()){
    filter::change_output(i->first);
  }
}


template <typename T>
inline bool get_filter_param(filter* f, const filter_params* params, const std::string& name, T& val)
{
    const filter_val* fv;
    std::stringstream ss;
    filter_params::const_iterator i;
    bool found = false;
    for (i = params->begin(); i != params->end(); ++i)
    {
        if (i->first == name)
        {
            fv = i->second;
            found = true;
            break;
        }
    }
    if (!found)
    {
        return false;
    }
    if (!get_filter_val(fv, val))
    {
        if (f)
        {
            ss << "parameter \"" << name << "\" has wrong type";
            f->set_status(ss.str());
        }
        return false;
    }
    return true;
}

/*
 This type of filter assumes a one-to-one mapping of outputs to input
 parameter sets. It's also assumed that each output is only dependent
 on one parameter set. This is in contrast to filters that perform some
 kind of quantification over its inputs; returning the closest object,
 for example.
*/
template <class T>
class map_filter : public typed_filter<T>
{
    public:
        map_filter(Symbol* root, soar_interface* si, filter_input* input)
          : typed_filter<T>(root, si, input)
        {}
        
        /*
         All created filter_vals are owned by the output list and cleaned
         up there, so don't do it here.
        */
        virtual ~map_filter() {}
        
        /*
         * Compute the output from parameters. 
         * If compute is successful, set out to be the desired 
         * output value, and return true
         * If an error occurs, return false
         */
        virtual bool compute(const filter_params* params, T& out) = 0;
        
        bool update_outputs(){
            const filter_input* input = filter::get_input();
            
            for (int i = input->first_added(); i < input->num_current(); ++i)
            {
                const filter_params* params = input->get_current(i);
                T out;
                if(!compute(params, out)){
                  return false;
                }
                add_output(params, out);
            }
            for (int i = 0; i < input->num_changed(); ++i)
            {
                const filter_params* params = input->get_changed(i);
                T out;
                if(!compute(params, out)){
                  return false;
                }
                update_output(params, out);
            }
            for (int i = 0; i < input->num_removed(); ++i)
            {
                const filter_params* params = input->get_removed(i);
                typed_filter<T>::remove_output(params);
            }
            return true;
        }
};

/*
 * This filter is very similar to a map filter, the only difference
 * being that every output must be selected, if for a given 
 * filter_params input the selected flag is set to false, then 
 * there will be no output for that input set
 *
 * This is useful when returning a subset of the input
 * (return all nodes that satisfy some condition)
*/
template <class T>
class select_filter : public typed_filter<T>
{
    public:
        select_filter(Symbol* root, soar_interface* si, filter_input* input)
          : typed_filter<T>(root, si, input)
        {}
        
        virtual ~select_filter() {}
        
        /*
         * Compute the output from parameters. 
         * If compute is successful, set out to be the desired 
         *   output value, and return true
         * If an error occurs, return false
         * The out value will only be added to the filter output
         *   if select is set to true
         */
        virtual bool compute(const filter_params* params, T& out, bool& select) = 0;
        
        
        bool update_outputs(){
            const filter_input* input = filter::get_input();
            
            for (int i = input->first_added(); i < input->num_current(); ++i)
            {
                const filter_params* params = input->get_current(i);
                T out;
                bool selected;
                if(!compute(params, out, selected)){
                  return false;
                }
                if(selected){
                  active_outputs.insert(params);
                  add_output(params, out);
                }
            }
            for (int i = 0; i < input->num_changed(); ++i)
            {
                const filter_params* params = input->get_changed(i);
                T out;
                bool selected;
                if(!compute(params, out, selected)){
                  return false;
                }
                if(set_has(active_outputs, params)){
                  if(selected){
                    // Previously and currently selected - update
                    update_output(params, out);
                  } else {
                    // Previously but not currently selected - remove
                    active_outputs.erase(params);
                    typed_filter<T>::remove_output(params);
                  }
                } else {
                  if(selected){
                    // Not previously but currently selected - add
                    active_outputs.insert(params);
                    add_output(params, out);
                  } else {
                    // Not previously or currently selected - do nothing
                  }
                }
                
                update_output(params, out);
            }
            for (int i = 0; i < input->num_removed(); ++i)
            {
                const filter_params* params = input->get_removed(i);
                active_outputs.erase(params);
                typed_filter<T>::remove_output(params);
            }
            return true;
        }

    private:
        std::set<const filter_params*> active_outputs;
};


/*
 This type of filter processes all inputs and produces a single
 output.
*/
template<typename T>
class reduce_filter : public typed_filter<T>
{
    public:
        reduce_filter(Symbol* root, soar_interface* si, filter_input* input)
            : typed_filter<T>(root, si, input), active_output(false)
        {}
        
        virtual ~reduce_filter() {}
        
        bool update_outputs()
        {
            const filter_input* input = filter::get_input();
            bool changed = false;
            
            for (int i = input->first_added(); i < input->num_current(); ++i)
            {
                if (!input_added(input->get_current(i)))
                {
                    return false;
                }
                changed = true;
            }
            for (int i = 0; i < input->num_changed(); ++i)
            {
                if (!input_changed(input->get_changed(i)))
                {
                    return false;
                }
                changed = true;
            }
            for (int i = 0; i < input->num_removed(); ++i)
            {
                if (!input_removed(input->get_removed(i)))
                {
                    return false;
                }
                changed = true;
            }
            
            if (changed)
            {
                if (!calculate_value(value))
                {
                    return false;
                }
            }

            if(input->num_current() == 0){
              // No inputs - remove if active
              if(active_output){
                typed_filter<T>::remove_output(NULL);
                active_output = false;
              }
            } else if(changed && active_output){
              // Changed value
              update_output(NULL, value);
            } else if(changed && !active_output){
              // New value
              add_output(NULL, value);
              active_output = true;
            }
            
            return true;
        }
        
    private:
        /**
         * Calculate the single output value and assign to val
         * Return true if successful
         */
        virtual bool calculate_value(T& val) = 0;

        /**
         * These are called when the inputs change
         * Use to keep a list of all the current inputs and
         * respond to changes
         */
        virtual bool input_added(const filter_params* params) = 0;
        virtual bool input_changed(const filter_params* params) = 0;
        virtual bool input_removed(const filter_params* params) = 0;
        
        bool active_output;
        T value;
};

class rank_filter : public typed_filter<double>
{
    public:
        rank_filter(Symbol* root, soar_interface* si, filter_input* input)
            : typed_filter<double>(root, si, input), best_input(NULL)
        {}
        
        virtual bool rank(const filter_params* params, double& r) = 0;
        
    private:

        virtual bool update_outputs()
        {
            const filter_input* input = filter::get_input();
            double r;
            const filter_params* p;

            bool changed;
          
            // Added inputs
            for (int i = input->first_added(); i < input->num_current(); ++i)
            {
                p = input->get_current(i);
                if (!rank(p, r))
                {
                    return false;
                }
                elems[p] = r;
                changed = true;
            }
            
            // Changed inputs
            for (int i = 0; i < input->num_changed(); ++i)
            {
                p = input->get_changed(i);
                if (!rank(p, r))
                {
                    return false;
                }
                elems[p] = r;
                changed = true;
            }

            // Removed inputs
            for (int i = 0; i < input->num_removed(); ++i)
            {
                p = input->get_removed(i);
                elems.erase(p);
                changed = true;
            }
            
            if (changed && !elems.empty())
            {
              // Calculate the best value
              const filter_params* cur_best = elems.begin()->first;
              double max_val = elems.begin()->second;

              std::map<const filter_params*, double>::iterator i;
              for(i = elems.begin(); i != elems.end(); i++){
                if(i->second > max_val){
                  cur_best = i->first;
                  max_val = i->second;
                }
              }

              if(best_input == NULL){
                // No previous output, add the current best
                best_input = cur_best;
                add_output(best_input, max_val);
              } else if(cur_best != best_input){
                // The best input has changed, remove the old and add the new
                remove_output(best_input);
                best_input = cur_best;
                add_output(best_input, max_val);
              } else {
                // The best input is the same, update the value
                update_output(best_input, max_val);
              }
            } else if(changed && best_input != NULL){
              // Nothing to rank, remove existing output
              remove_output(best_input);
              best_input = NULL;
            }

            return true;
        }
        
        std::map<const filter_params*, double> elems;
        const filter_params* best_input;
};

/*
 Filters that don't take any inputs and always outputs the same value
*/
template <class T>
class const_filter : public typed_filter<T>
{
    public:
        const_filter(const T& v) : typed_filter<T>(NULL, NULL, NULL), added(false), v(v) {}
        
        
        bool update_outputs()
        {
            if (!added)
            {
                typed_filter<T>::add_output(NULL, v);
                added = true;
            }
            return true;
        }
        
    private:
        T v;
        bool added;
};

/*
 Passes an arbitrary element in each input parameter set to the output
 list. This filter is intended to be used with concat_filter_input to
 implement a "combine" filter that multiplexes an arbitrary number of
 inputs into a single list.
*/
template <class T>
class passthru_filter : public map_filter<T>
{
    public:
        passthru_filter(Symbol* root, soar_interface* si, filter_input* input)
            : map_filter<T>(root, si, input)
        {}

        bool compute(const filter_params* params, T& out){
          if(params->empty()){
            return false;
          }
          filter_val* fv = params->begin()->second;
          return get_filter_param(fv, out);
        }
};

#endif
