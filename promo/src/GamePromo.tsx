import React from "react";
import { AbsoluteFill } from "remotion";
import { TransitionSeries, linearTiming } from "@remotion/transitions";
import { slide } from "@remotion/transitions/slide";
import { fade } from "@remotion/transitions/fade";
import { GameHook } from "./scenes/game/GameHook";
import { AgentShowcase } from "./scenes/game/AgentShowcase";
import { GameplayPreview } from "./scenes/game/GameplayPreview";
import { GovernanceChallenge } from "./scenes/game/GovernanceChallenge";
import { PlayNow } from "./scenes/game/PlayNow";
import { colors } from "./theme";

const T = 15; // transition duration in frames

// Scene durations: 150 + 210 + 240 + 210 + 240 = 1050
// Minus 4 transitions: 1050 - 4 * 15 = 990 visible frames
// Total composition: 1050 frames (35s at 30fps)

export const GamePromo: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: colors.bg }}>
      <TransitionSeries>
        <TransitionSeries.Sequence durationInFrames={150}>
          <GameHook />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-bottom" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={210}>
          <AgentShowcase />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={240}>
          <GameplayPreview />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={slide({ direction: "from-right" })}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={210}>
          <GovernanceChallenge />
        </TransitionSeries.Sequence>

        <TransitionSeries.Transition
          presentation={fade()}
          timing={linearTiming({ durationInFrames: T })}
        />
        <TransitionSeries.Sequence durationInFrames={240}>
          <PlayNow />
        </TransitionSeries.Sequence>
      </TransitionSeries>
    </AbsoluteFill>
  );
};
