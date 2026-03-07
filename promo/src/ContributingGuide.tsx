import React from "react";
import { AbsoluteFill } from "remotion";
import { TransitionSeries, linearTiming } from "@remotion/transitions";
import { slide } from "@remotion/transitions/slide";
import { fade } from "@remotion/transitions/fade";
import { Welcome } from "./scenes/contributing/Welcome";
import { ForkAndClone } from "./scenes/contributing/ForkAndClone";
import { DevSetup } from "./scenes/contributing/DevSetup";
import { FindIssue } from "./scenes/contributing/FindIssue";
import { ProjectStructure } from "./scenes/contributing/ProjectStructure";
import { MakeChanges } from "./scenes/contributing/MakeChanges";
import { SubmitPR } from "./scenes/contributing/SubmitPR";
import { ClosingCTA } from "./scenes/contributing/ClosingCTA";
import { colors } from "./theme";

const T = 15; // transition duration in frames

// Scene durations: 180+180+180+165+165+180+195+150 = 1395
// Minus 7 transitions: 1395 - 105 = 1290 total frames (43s at 30fps)

export const ContributingGuide: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: colors.bg }}>
      <TransitionSeries>
        <TransitionSeries.Sequence durationInFrames={180}>
          <Welcome />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={180}>
          <ForkAndClone />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={180}>
          <DevSetup />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={165}>
          <FindIssue />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={165}>
          <ProjectStructure />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={180}>
          <MakeChanges />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={195}>
          <SubmitPR />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={fade()}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={150}>
          <ClosingCTA />
        </TransitionSeries.Sequence>
      </TransitionSeries>
    </AbsoluteFill>
  );
};
