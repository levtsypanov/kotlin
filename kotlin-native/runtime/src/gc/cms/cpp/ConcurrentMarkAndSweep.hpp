/*
 * Copyright 2010-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the LICENSE file.
 */

#pragma once

#include <atomic>
#include <cstddef>

#include "Allocator.hpp"
#include "GCScheduler.hpp"
#include "IntrusiveList.hpp"
#include "ObjectFactory.hpp"
#include "ScopedThread.hpp"
#include "Types.h"
#include "Utils.hpp"
#include "GCState.hpp"
#include "std_support/Memory.hpp"

namespace kotlin {

namespace mm {
class ThreadData;
}

namespace gc {

class FinalizerProcessor;

// Stop-the-world mark + concurrent sweep. The GC runs in a separate thread, finalizers run in another thread of their own.
class ConcurrentMarkAndSweep : private Pinned {
public:
    class ObjectData {
        static inline constexpr unsigned colorMask = (1 << 1) - 1;

    public:
        enum class Color : unsigned {
            kWhite = 0, // Initial color at the start of collection cycles. Objects with this color at the end of GC cycle are collected.
                        // All new objects are allocated with this color.
            kBlack, // Objects encountered during mark phase.
        };

        Color color() const noexcept { return static_cast<Color>(getPointerBits(next_.load(), colorMask)); }
        void setColor(Color color) noexcept { next_ = setPointerBits(clearPointerBits(next_.load(), colorMask), static_cast<unsigned>(color)); }
        bool atomicSetToBlack() noexcept {
            ObjectData* before = next_.load();
            if (getPointerBits(before, colorMask) != static_cast<unsigned>(Color::kWhite))
                return false;
            ObjectData* black = setPointerBits(before, static_cast<unsigned>(Color::kBlack));
            bool success = next_.compare_exchange_strong(before, black);
            RuntimeAssert(success || hasPointerBits(before, colorMask), "next_ must have been marked black");
            return success;
        }

        ObjectData* next() const noexcept { return clearPointerBits(next_.load(), colorMask); }
        void setNext(ObjectData* next) noexcept {
            RuntimeAssert(!hasPointerBits(next, colorMask), "next must be untagged: %p", next);
            auto bits = getPointerBits(next_.load(), colorMask);
            next_ = setPointerBits(next, bits);
        }

    private:
        // Color is encoded in low bits.
        std::atomic<ObjectData*> next_ = nullptr;
    };

    struct MarkQueueTraits {
        static ObjectData* next(const ObjectData& value) noexcept { return value.next(); }

        static void setNext(ObjectData& value, ObjectData* next) noexcept { value.setNext(next); }
    };

    using MarkQueue = intrusive_forward_list<ObjectData, MarkQueueTraits>;

    class ThreadData : private Pinned {
    public:
        using ObjectData = ConcurrentMarkAndSweep::ObjectData;
        using Allocator = AllocatorWithGC<Allocator, ThreadData>;

        explicit ThreadData(ConcurrentMarkAndSweep& gc, mm::ThreadData& threadData, GCSchedulerThreadData& gcScheduler) noexcept :
            gc_(gc), gcScheduler_(gcScheduler) {}
        ~ThreadData() = default;

        void SafePointAllocation(size_t size) noexcept;

        void ScheduleAndWaitFullGC() noexcept;
        void ScheduleAndWaitFullGCWithFinalizers() noexcept;

        void OnOOM(size_t size) noexcept;
        void Mark() noexcept;

        Allocator CreateAllocator() noexcept { return Allocator(gc::Allocator(), *this); }

    private:
        ConcurrentMarkAndSweep& gc_;
        GCSchedulerThreadData& gcScheduler_;
    };

    using Allocator = ThreadData::Allocator;

    ConcurrentMarkAndSweep(mm::ObjectFactory<ConcurrentMarkAndSweep>& objectFactory, GCScheduler& scheduler) noexcept;
    ~ConcurrentMarkAndSweep();

    void StartFinalizerThreadIfNeeded() noexcept;
    void StopFinalizerThreadIfRunning() noexcept;
    bool FinalizersThreadIsRunning() noexcept;

private:
    // Returns `true` if GC has happened, and `false` if not (because someone else has suspended the threads).
    bool PerformFullGC(int64_t epoch) noexcept;

    mm::ObjectFactory<ConcurrentMarkAndSweep>& objectFactory_;
    GCScheduler& gcScheduler_;

    uint64_t lastGCTimestampUs_ = 0;
    GCStateHolder state_;
    ScopedThread gcThread_;
    std_support::unique_ptr<FinalizerProcessor> finalizerProcessor_;

    MarkQueue markQueue_;
    std::atomic<unsigned> aliveHeapSetBytes_ = 0;
};

} // namespace gc
} // namespace kotlin
