//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

#include "bsqmap_decl.h"

#pragma once

namespace BSQ
{
template <typename Ty, typename K, typename K_RCDecF, typename K_DisplayF, typename K_CMP, typename K_EQ, typename V, typename V_RCDecF, typename V_DisplayF>
class BSQMapOps
{
public:
    template <typename ListT, typename K_RCIncF, MIRNominalTypeEnum ntype>
    static ListT* map_key_list(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> K {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename SetT, typename K_RCIncF, MIRNominalTypeEnum ntype>
    static SetT* map_key_set(Ty* m)
    {
        std::vector<K> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> K {
            return K_RCIncF{}(v.key);
        });

        return BSQ_NEW_NO_RC(SetT, ntype, move(entries));
    }

    template <typename ListT, typename V_RCIncF, MIRNominalTypeEnum ntype>
    static ListT* map_values(Ty* m)
    {
        std::vector<V> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> V {
            return V_RCIncF{}(v.value);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename ListT, typename MapEntryT, MIRNominalTypeEnum ntype, typename LambdaMEC>
    static ListT* map_entries(Ty* m, LambdaMEC lmec)
    {
        std::vector<MapEntryT> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [lmec](MEntry<K, V>& v) -> MapEntryT {
            return lmec(v.key, v.value);
        });

        return BSQ_NEW_NO_RC(ListT, ntype, move(entries));
    }

    template <typename ListT>
    static BSQBool map_has_all(Ty* m, ListT* kl)
    {
        return std::all_of(kl->entries.begin(), kl->entries.end(), [m](K k) -> bool {
            return m->hasKey(k);
        });
    }

    template <typename SetT>
    static BSQBool map_domainincludes(Ty* m, SetT* s)
    {
        return std::all_of(s->entries.begin(), s->entries.end(), [m](K k) -> bool {
            return m->hasKey(k);
        });
    }

    template <typename K_RCIncF, typename V_RCIncF, typename LambdaP>
    static Ty* map_submap(Ty* m, LambdaP p)
    {
        std::vector<MEntry<K, V>> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [p, &entries](MEntry<K, V>& v) {
            if(p(v.key, v.value))
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(v.key), V_RCIncF{}(v.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename RMType, typename RMEntryType, MIRNominalTypeEnum ntype, typename LambdaTCK, typename LambdaTCV, typename LambdaCC>
    static RMType* map_oftype(Ty* m, LambdaTCK tck, LambdaTCV tcv, LambdaCC cc)
    {
        std::vector<RMEntryType> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [tck, tcv, cc, &entries](MEntry<K, V>& v) {
            if(tck(v.key) && tcv(v.value))
            {
                entries.push_back(cc(v.key, v.value));
            }
        });

        return BSQ_NEW_NO_RC(RMType, ntype, move(entries));
    }

    template <typename RMType, typename RMEntryType, MIRNominalTypeEnum ntype, typename LambdaTCK, typename LambdaTCV, typename LambdaCC>
    static RMType* map_cast(Ty* m, LambdaTCK tck, LambdaTCV tcv, LambdaCC cc)
    {
        std::vector<RMEntryType> entries;
        std::for_each(m->entries.begin(), m->entries.end(), [tck, tcv, cc, &entries](MEntry<K, V>& v) {
            BSQ_ASSERT(tck(v.key) && tcv(v.value), "abort -- invalid element in cast in Map<K, V>::cast");

            entries.push_back(cc(v.key, v.value));
        });

        return BSQ_NEW_NO_RC(RMType, ntype, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_projectall(Ty* m, ListT* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(dl->entries.begin(), dl->entries.end(), [&entries, m](K k) {
            V vv;
            if(m->tryGetValue(k, &vv))
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(k), V_RCIncF{}(vv)});
            }
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V, K_CMP>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_excludeall(Ty* m, ListT* dl)
    {
        std::vector<MEntry<K, V>> entries;

        std::set<K, K_CMP> es(dl->entries.begin(), dl->entries.end());
        std::for_each(m->entries.begin(), m->entries.end(), [&entries, &es](MEntry<K, V>& e) {
            bool has = es.find(e.key) != es.end();
            if(!has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(e.key), V_RCIncF{}(e.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename SetT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_project(Ty* m, SetT* ds)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(ds->entries.begin(), ds->entries.end(), [&entries, m](K k) {
            V vv;
            if(m->tryGetValue(k, &vv))
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(k), V_RCIncF{}(vv)});
            }
        });

        std::stable_sort(entries.begin(), entries.end(), MEntryCMP<K, V, K_CMP>{});
        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename SetT, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_exclude(Ty* m, SetT* ds)
    {
        std::vector<MEntry<K, V>> entries;

        std::for_each(m->entries.begin(), m->entries.end(), [&entries, ds](MEntry<K, V>& e) {
            bool has = ds->has(e.key);
            if(!has)
            {
                entries.push_back(MEntry<K, V>{K_RCIncF{}(e.key), V_RCIncF{}(e.value)});
            }
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename K_RCIncF, typename U, typename U_RCDecF, typename U_DisplayF, MIRNominalTypeEnum ntype, typename LambdaF>
    static BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, U, U_RCDecF, U_DisplayF>* map_remap(Ty* m)
    {
        std::vector<MEntry<K, V>> entries;
        entries.reserve(m->entries.size());

        std::transform(m->entries.begin(), m->entries.end(), std::back_inserter(entries), [](MEntry<K, V>& v) -> MEntry<K, V> {
            return MEntry<K, U>{K_RCIncF{}(v.key), LambdaF{}(v.key, v.value)};
        });

        return BSQ_NEW_NO_RC((BSQMap<K, K_RCDecF, K_DisplayF, K_CMP, K_EQ, U, U_RCDecF, U_DisplayF>), ntype, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_union(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> std::pair<K, V> {
            BSQ_ASSERT(rm.find(e.key) == rm.end(), "abort -- cannot have duplicate keys in Map<K, V>::union");

            rm.insert(e.key, e.value);
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, MIRNominalTypeEnum ntype, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_unionall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::transform(maps.begin()->entries.begin(), maps.begin()->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(maps.begin() + 1, maps.end(), [&rm](Ty* om) {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) {
                BSQ_ASSERT(rm.find(e.key) == rm.end(), "abort -- cannot have duplicate keys in Map<K, V>::unionAll");

                rm.insert(e.key, e.value);
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }

    template <typename K_RCIncF, typename V_RCIncF>
    static Ty* map_merge(Ty* m, Ty* om)
    {
        std::map<K, V, K_CMP> rm;

        std::transform(m->entries.begin(), m->entries.end(), std::inserter(rm, rm.end()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) -> std::pair<K, V> {
            rm.insert(e.key, e.value);
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, m->nominalType, move(entries));
    }

    template <typename ListT, MIRNominalTypeEnum ntype, typename K_RCIncF, typename V_RCIncF>
    static Ty* map_mergeall(ListT* dl)
    {
        std::map<K, V, K_CMP> rm;
        std::vector<Ty*>& maps = dl->entries;

        std::transform(maps.begin()->entries.begin(), maps.begin()->entries.end(), std::inserter(rm, rm.begin()), [](MEntry<K, V>& e) -> std::pair<K, V> {
            return std::make_pair(e.key, e.value);
        });

        std::for_each(maps.begin() + 1, maps.end(), [&rm](Ty* om) {
            std::for_each(om->entries.begin(), om->entries.end(), [&rm](MEntry<K, V>& e) {
                rm.insert(e.key, e.value);
            });
        });

        std::vector<MEntry<K, V>> entries;
        std::transform(rm->entries.begin(), rm->entries.end(), std::back_inserter(entries), [](std::pair<K, V>& e) -> MEntry<K, V> {
            return MEntry<K, V>(K_RCIncF{}(e.key), V_RCIncF{}(e.value));
        });

        return BSQ_NEW_NO_RC(Ty, ntype, move(entries));
    }
};
}
