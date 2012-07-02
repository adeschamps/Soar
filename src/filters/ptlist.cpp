#include <list>
#include "filter.h"
#include "sgnode.h"
#include "linalg.h"
#include "scene.h"

using namespace std;

class node_ptlist_filter : public typed_map_filter<ptlist*> {
public:
	node_ptlist_filter(filter_input *input, bool local) : typed_map_filter<ptlist*>(input), local(local) {}
	
	~node_ptlist_filter() {
		std::list<ptlist*>::iterator i;
		for (i = lists.begin(); i != lists.end(); ++i) {
			delete *i;
		}
	}
	
	bool compute(const filter_param_set *params, bool adding, ptlist *&res, bool &changed) {
		const sgnode *n;
		if (!get_filter_param(this, params, "node", n)) {
			return false;
		}
		const convex_node *cn = dynamic_cast<const convex_node*>(n);
		if (!cn) {
			return false;
		}
		if (adding) {
			res = new ptlist();
			lists.push_back(res);
		}
		
		if (local) {
			changed = (*res != cn->get_local_points());
			*res = cn->get_local_points();
		} else {
			changed = (*res != cn->get_world_points());
			*res = cn->get_world_points();
		}
		return true;
	}
	
	void result_removed(ptlist *&res) {
		lists.remove(res);
		delete res;
	}
	
private:
	bool local;
	std::list<ptlist*> lists;
};

filter* _make_local_filter_(scene *scn, filter_input *input) {
	return new node_ptlist_filter(input, true);
}

filter* _make_world_filter_(scene *scn, filter_input *input) {
	return new node_ptlist_filter(input, false);
}

class ptlist_filter : public typed_map_filter<ptlist*> {
public:
	ptlist_filter(filter_input *input) : typed_map_filter<ptlist*>(input) {}
	
	~ptlist_filter() {
		std::list<ptlist*>::iterator i;
		for (i = lists.begin(); i != lists.end(); ++i) {
			delete *i;
		}
	}
	
	bool compute(const filter_param_set *params, bool adding, ptlist *&res, bool &changed) {
		filter_param_set::const_iterator i;
		ptlist newres;
		
		for(i = params->begin(); i != params->end(); ++i) {
			vec3 v;
			if (!get_filter_val(i->second, v)) {
				set_error("all parameters must be vec3's");
				return false;
			}
			newres.push_back(v);
		}
		
		if (adding) {
			res = new ptlist();
			lists.push_back(res);
		}
		changed = (newres != *res);
		*res = newres;
		return true;
	}
	
	void result_removed(ptlist *&res) {
		lists.remove(res);
		delete res;
	}
	
private:
	std::list<ptlist*> lists;
};

filter* _make_ptlist_filter_(scene *scn, filter_input *input) {
	return new ptlist_filter(input);
}
